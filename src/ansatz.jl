function split_terms(S, x) 	
	S = unique([x; [equivalent(t, x) for t in terms(S) if isdependent(t,x)]])
	p = sortperm(complexity.(S))
	return S[p]
end

function split_terms(S, x, ω) 	
	D = Dict()
	c = collect_powers(S, ω)

	for (k, y) in c
		ts = split_terms(y, x)
		for t in ts			
			for r in terms(expand(t))
				if haskey(D, r)
					push!(D[r], k)
				else
					D[r] = [k]
				end
			end
		end
	end
	
	# S = sum(sum.(split_terms.(values(c), x)))
	# S = unique([x; [equivalent(t, x) for t in terms(S) if isdependent(t,x)]])	
	S = collect(keys(D))
	K = collect(values(D))
	p = sortperm(complexity.(S))
	return S[p], K[p]
end

@syms z

function generate_mixer(eq, x)
    eq = eq isa Num ? eq.val : eq
    x = x isa Num ? x.val : x

    p = transform(eq, x)
 	q, sub, ks = rename_factors(p, (si => Si, ci => Ci, ei => Ei, li => Li))
 	
 	if sum(ks) > 8	# number of ansatz is exponential in sum(ks)
 		return [x, eq], [[0], [0]]
 	end
 	
    S = 1
    R = 0
    D = Differential(x)

    for i in 1:length(ks)    	
        μ = u[i]
        λ = sub[μ]
        Iμ, dμ = apply_partial_int_rules(λ, x)
        U = substitute(Iμ, sub)
        dU = expand_derivatives(D(λ)) / dμ    

		k = ks[i]
        R = expand((U/ω + λ + dU*ω) ^ k)
        # R = sum(U^p * dU^q * λ^r * ω^(q-p) for p=0:k for q=0:k for r=0:k if p+q+r==k)
        
        if isdependent(dμ, x)
	        R = sum(t + t/dμ for t in terms(R))
	    end
	    
        S = expand(S * R)
    end    
    
    S, K = split_terms(S, x, ω)        
    return S, K
end


function populate_matrix(X, eq, x, basis, radius, complex_plane; abstol = 1e-6, differentiate=false)
    n = length(basis)
    m = length(X)

    # A is an nxn matrix holding the values of the fragments at n random points
    A = zeros(Complex{Float64}, (m, n))
    
    fn = fun!(eq, x)
    gn = differentiate ? deriv_fun!.(basis, x) : fun!.(basis, x)

    k = 1
    l = 10 * m # max attempt

    while k <= m && l > 0
        try
            b₀ = fn(X[k])

            if is_proper(b₀)
                for j in 1:n
                    A[k, j] = gn[j](X[k]) / b₀
                end
                if all(is_proper, A[k, :])
                    k += 1
                end
            end
        catch e
            println("Error from populate_matrix: ", e)
        end
        l -= 1
    end

    return A
end

function init_basis_matrix_dual(eq, x, S, R, radius, complex_plane; abstol = 1e-6)
    n = length(R) + length(S)

    # A is an nxn matrix holding the values of the fragments at n random points
    A = zeros(Complex{Float64}, (n, n))
    X = zeros(Complex{Float64}, n)

    fn = fun!(eq, x)
    gn = vcat(deriv_fun!.(S, x), fun!.(R, x))

    k = 1
    l = 10 * n# max attempt

    while k <= n && l > 0
        try
            x₀ = test_point(complex_plane, radius)
            X[k] = x₀
            b₀ = fn(X[k])

            if is_proper(b₀)
                for j in 1:n
                    A[k, j] = gn[j](X[k]) / b₀
                end
                if all(is_proper, A[k, :])
                    k += 1
                end
            end
        catch e
            println("Error from init_basis_matrix_dual: ", e)
        end
        l -= 1
    end

    return A, X
end

function init_basis_matrix_lower(eq, x, S, radius, complex_plane; abstol = 1e-6)
    n = length(S)

    # A is an nxn matrix holding the values of the fragments at n random points
    A = zeros(Complex{Float64}, (n, n))
    X = zeros(Complex{Float64}, n)

    fn = fun!(eq, x)
    gn = fun!.(S, x)

    k = 1
    l = 10 * n# max attempt

    while k <= n && l > 0
        try
            x₀ = test_point(complex_plane, radius)
            X[k] = x₀
            b₀ = fn(X[k])

            if is_proper(b₀)
                for j in 1:n
                    A[k, j] = gn[j](X[k]) / b₀
                end
                if all(is_proper, A[k, :])
                    k += 1
                end
            end
        catch e
            println("Error from init_basis_matrix_dual: ", e)
        end
        l -= 1
    end

    return A, X
end



function sparse_fit(A, opt; abstol = 1e-6)
    n, m = size(A)

	b = ones((1, n))
    solver = SparseLinearSolver(opt,
                                    options = DataDrivenCommonOptions(verbose = false,
                                                                      maxiters = 1000))
    res, _... = solver(A', b)
    q₀ = DataDrivenSparse.coef(first(res))
	q = nice_parameter.(q₀)    
    
    if sum(iscomplex.(q)) > 1
    	return nothing, Inf
    end   # eliminating complex coefficients

      ϵ = abs(rms(A * q₀' .- 1))
	return q, ϵ
end

final_result(q, basis) = sum(q[i] * expr(basis[i]) for i in 1:length(basis) if q[i] != 0; init = 0)
final_basis(q, basis) = [expr(basis[i]) for i in 1:length(basis) if q[i] != 0]

#############################################################################

function try_basis(eq, x, basis, K=nothing; abstol=1e-6, opt=STLSQ(exp.(-10:1:0)), complex_plane=true, radius=1.0) 
	A, X = init_basis_matrix(eq, x, basis, radius, complex_plane; abstol) 			
	l = find_independent_subset(A; abstol)
    A, basis = A[l, l], basis[l]
	
	q, ϵ = sparse_fit(A, opt)	
	
	if ϵ < abstol
		if K != nothing
			for i in 1:length(q)
				if q[i] != 0
					println(basis[i], " --> ", K[i])
				end
			end
		end
		return final_result(q, basis), ϵ
	else
		return nothing, ϵ
	end
end

function lower_basis(eq, x, basis)
	S = sum(basis) - equivalent(eq, x)
	return split_terms(expand_derivatives(S + Differential(x)(S)), x)
end

function upper_basis(x, S, R) 
	L = []
	for eq in R
		println(eq)
		s, r = generate_homotopy_residue(eq, x)
		append!(S, s)
		append!(L, r)
	end	
	return S, L
end

function filter_unsolvable(x, S, R; abstol=1e-6, opt=STLSQ(exp.(-10:1:0)), complex_plane=true, radius=1.0)
	A₀, X = init_basis_matrix(1, x, S, radius, complex_plane; abstol) 			
	RR = []
	
	for y in R
		fn = fun!.(y, x)
		A = similar(A₀)
		for k = 1:length(X)
			A[k, :] .= A₀[k, :] / fn(X[k])
		end
		q, ϵ = sparse_fit(A, opt)
		if ϵ > abstol
			push!(RR, y)
		end
	end
	
	return RR
end

function solve_mixer(eq, x; kwargs...)    
	args = Dict(kwargs)
    abstol, opt, complex_plane, radius, num_trials, num_steps = 
    									 args[:abstol], args[:opt], 
    									 args[:complex_plane], args[:radius],
    									 args[:num_trials], args[:num_steps]

	S, K = generate_mixer(eq, x)
	S = cache.(S)
	sp = .!is_special.(expr.(S))	

	# y, ϵ = try_basis(eq, x, S[sp], K[sp])	
	
	for i = 1:num_trials	
		y, ϵ = try_basis(eq, x, S[sp], K[sp])
		if ϵ < abstol 	
			printstyled("S0\n"; color=:red)		
			return y, 0, ϵ
		end
	end		
	
	for i = 1:num_trials	
		y, ϵ = try_basis(eq, x, S, K)
		if ϵ < abstol 	
			printstyled("Sp\n"; color=:red)
			return y, 0, ϵ
		end
	end	

	for j = 2:num_steps	
		s = sum(expr.(S))
		S, K = split_terms((1+x)*(s + ω*expand_derivatives(Differential(x)(s))), x, ω)		

		for i = 1:num_trials	
			y, ϵ = try_basis(eq, x, S)
			if ϵ < abstol 	
				printstyled("S+\n"; color=:red)
				return y, 0, ϵ
			end
		end
	end
	
	return 0, eq, Inf		
end

########################################################################

sp_rules = [@rule +(~~xs) => sum(~~xs)
           @rule *(~~xs) => sum(~~xs)
           @rule ~x / ~y => ~x + ~y
           @rule ^(~x, ~y) => ~x + ~y
           @rule Si(~x) => ω
           @rule Ci(~x) => ω
           @rule Li(~x) => ω
           @rule Ei(~x) => ω
           @rule (~f)(~x) => 0
           # @rule ~x => 0
           ]

function is_special(eq)
    _, eq = ops(eq)
    h = Prewalk(PassThrough(Chain(sp_rules)))(eq)
    return any(x -> isequal(x, ω), get_variables(h))
end

function filter_special_functions(S, contain=false)
	if contain
		return filter(x -> is_special(expr(x)), S)
	else
		return filter(x -> !is_special(expr(x)), S)
	end
end

############################################################################

function distribute(::Div, eq)
    a = arguments(eq)[1]
    b = arguments(eq)[2]
    return sum(terms(a) ./ b)
end

function distribute(::Add, eq)
    return sum(distribute.(terms(eq)))
end

distribute(::Any, eq) = eq

distribute(eq) = distribute(ops(expand(eq))...)

##############################################################################

has_log_rules = [
	@rule +(~~xs) => sum(~~xs)
	@rule *(~~xs) => sum(~~xs)
	@rule ~x / ~y => ~x + ~y
	@rule ~x - ~y => ~x + ~y
	@rule log(~x) => ω
	@rule (~f)(~x) => 0
]

function has_log(eq) 
	eq = last(ops(eq))
	w = Prewalk(PassThrough(Chain(has_log_rules)))(eq)
	return any(x -> isequal(x, ω), get_variables(w))
end

