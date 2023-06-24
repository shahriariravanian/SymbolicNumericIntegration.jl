strip_num(x) = x isa Num ? x.val : x

function split_terms(S, x) 	
	S = unique([equivalent(t, x) for t in terms(S) if isdependent(t,x)])    
    return isempty(S) ? [1] : S	
    # p = sortperm(complexity.(S))
	# return S[p]
end

function split_terms(S, x, ω) 	
	D = Dict()
	c = collect_powers(S, ω)

	for (k, y) in c
		ts = split_terms(y, x)
		for t in ts			
			for r in split_terms(expand(t), x)
				if haskey(D, r)
					push!(D[r], k)
				else
					D[r] = [k]
				end
			end
		end
	end
	
	S = collect(keys(D))
	p = sortperm(complexity.(S))
	return S[p]
end

@syms z

function generate_mixer(eq, x)
	if istree(eq) && operation(eq) == +
		S = sum(sum(generate_mixer(t, x)) for t in terms(eq))
		return split_terms(S, x)
	end

    p = transform(eq, x)
 	q, sub, ks = rename_factors(p, (si => Si, ci => Ci, ei => Ei, li => Li))
 	
    S = 1
    D = Differential(x)

    for i in 1:length(ks)    	
        μ = u[i]
        λ = sub[μ]
        Iμ, dμ = apply_partial_int_rules(λ, x)
        U = substitute(Iμ, sub)
        dU = expand_derivatives(D(λ)) / dμ    

		k = ks[i]		
        R = expand((U/ω + λ + dU*ω) ^ k)        
        # R = substitute(R, Dict(ω => dμ))
        # R = sum(expand(U^p * dU^q * λ^r * ω^(q-p)) for p=0:k for q=0:k for r=0:k if p+q+r==k)
        
        if isdependent(dμ, x)
	        R = sum(t + t/dμ for t in terms(R))
	    end
	    
        S = expand(S * R)
    end    
    
    S = substitute(S, sub)
    
    return split_terms(S, x, ω)
end

function generate_mixer_ex(eq, x)
    eq, x = strip_num(eq), strip_num(x) 
	    
	S = 1
	F = create_artifacts(eq, x)	
	
	@syms α β
	
	for (μ, k, U, dU, dμ, ρ) in F
		R = expand((μ + α/ω + β*ω) ^ k)		
		R = substitute(R, Dict(α => U, β => dU))

		if isdependent(dμ, x)
	    	R = sum(t + t/dμ for t in terms(R))
	    end
	    
	    S = expand(S * R)
	end	
    
    return split_terms(S, x, ω)
end

function create_artifacts(eq, x)
    eq, x = strip_num(eq), strip_num(x) 

	if istree(eq) && operation(eq) == +
		return union([create_artifacts(t, x) for t in terms(eq)]...)
	end

    p = transform(eq, x)
 	q, sub, ks = rename_factors(p, (si => Si, ci => Ci, ei => Ei, li => Li))
 	
    D = Differential(x)
    
    F = []

    for i in 1:length(ks)    	
        μ = u[i]
   		k = ks[i]		
   		
        λ = sub[μ]
        Iμ, dμ = apply_partial_int_rules(λ, x)
        U = substitute(Iμ, sub)
        ρ = substitute(q/μ^k, sub)
        dU = expand_derivatives(D(λ)) / dμ    

        # f = expand(Iμ/ω + λ + dU*ω)        
	    push!(F, (λ, k, U, dU, dμ, ρ))	    
    end    
    
    return F
end

function expand_ansatz_basis(S, x)
	S = S
	σ = sum(expr.(S))
	# σ += x * σ
	
	for (i, eq) in enumerate(S)		
		σ += deriv!(eq, x)
	end 
	return split_terms(σ, x), true
end

#############################################################################

function populate_basis(eq, x)    
    eq = strip_num(eq)
    x = strip_num(x)
    
	θ = create_basis(eq, x)	
	S = generate_mixer(eq, x)	
	append_basis!(θ, S)
	
	return θ
end

function solve_mixer(eq, x; abstol=1e-6, opt=STLSQ(exp.(-10:1:0)), complex_plane=true, radius=5.0, num_trials=10, num_steps=3, kwargs...)    
	θ = populate_basis(eq, x)

	q, ϵ = sparse_fit(θ; abstol, opt)	
	
	if ϵ < abstol
		return final_result(q, θ), 0, ϵ
	end
	
	print(length(θ.S), " => ")
	contract!(θ)
	println(length(θ.S))
	E, ok = expand_ansatz_basis(θ.S, x)	# applying the f'f algorithm		
			
	if ok
		append_basis!(θ, [x; E])
	else
		return 0, eq, Inf	
	end		
			
	q, ϵ = sparse_fit(θ; abstol, opt)
		
	if ϵ < abstol
		println("expanded")
		return final_result(q, θ), 0, ϵ
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

##########################################################################

mutable struct Basis
    S::Array{ExprCache}
    A::Matrix{Complex{Float64}}
    X::Vector{Complex{Float64}}
    Y::Vector{Complex{Float64}}
    eq::ExprCache 
    x::SymbolicUtils.BasicSymbolic
end

basis(θ::Basis) = θ.basis

function copy!(dst::Basis, src::Basis)
    @assert isequal(dst.eq, src.eq) && isequal(dst.x, src.x)
    dst.A = src.A
    dst.X = src.X
    dst.Y = src.Y
    dst.S = src.S
end

function create_basis(eq, x, n=20; radius=5.0) 
    X = zeros(Complex{Float64}, n)
    Y = zeros(Complex{Float64}, n)
    A = zeros(Complex{Float64}, (n,1))
    
    eq = cache(eq)
    fn = fun!(eq, x)
    gn = deriv_fun!(eq, x)

	k = 1
	
    while k <= n        
        X[k] = test_point(true, radius)
        Y[k] = fn(X[k])
        A[k,1] = gn(X[k]) / Y[k]
        
        if is_proper(Y[k]) && is_proper(A[k,1])
        	k += 1
        end
    end 

    return Basis([eq], A, X, Y, eq, x)
end

function append_basis!(θ::Basis, L; abstol=1e-6)
    l = length(L)
    resize_basis!(θ, l)
    n, m = size(θ.A)
    L = cache.(L)    

    C = zeros(Complex{Float64}, (n, m+l))
    C[:,1:m] .= θ.A

    gn = deriv_fun!.(L, θ.x)

    for j = 1:l
        C[:, m+j] .= gn[j].(θ.X) ./ θ.Y
    end 
    
    S = vcat(θ.S, L)
    
    # remove bad columns
    cols = vec(all(is_proper.(C); dims=1))
    C = C[:, cols]
    S = S[cols]
           
    # remove bad rows
    rows = vec(all(is_proper.(C); dims=2))    
    C = C[rows, :]
     
    # remove linearly-dependent columns
   	cols = find_independent_subset(C; abstol)
    S, C = S[cols], C[:, cols]
    
    θ.S = S
    θ.A = C
end

function resize_basis!(θ::Basis, k=0; abstol=1e-6, radius=5.0)
    n, m = size(θ.A)

    if n < m+k
        θ2 = create_basis(θ.eq, θ.x, 2*(m+k); radius)
        append_basis!(θ2, θ.S[2:end]; abstol)
        copy!(θ, θ2)
    end    
end

function randomize!(θ::Basis; abstol=1e-6, radius=5.0)
    n, m = size(θ.A)
    θ2 = create_basis(θ.eq, θ.x, m; radius)
    append_basis!(θ2, θ.S[2:end]; abstol)
    copy!(θ, θ2)    
end

function filter_integrand!(θ::Basis, L, indep=true; abstol=1e-6)
    l = length(L)
    resize_basis!(θ, l)
    n, m = size(θ.A)
    
    C = zeros(Complex{Float64}, (n, m+l))
    C[:,1:m] .= θ.A

    gn = fun!.(cache.(L), θ.x)    # note, fun! instead of deriv_fun! here

    for j = 1:l
        C[:, m+j] .= gn[j].(θ.X) ./ θ.Y
    end    
     
    # remove linearly-dependent integrands
    cols = find_independent_subset(C; abstol)
    if !indep
    	cols = .!cols
    end
    return L[cols[m+1:end]]
end

function contract!(θ::Basis; abstol=1e-3)    
    resize_basis!(θ, length(θ.S))
    n, m = size(θ.A)
    
    C = zeros(Complex{Float64}, (n, 2m))
    C[:,1:m] .= θ.A

    gn = fun!.(θ.S, θ.x)    # note, fun! instead of deriv_fun! here

    for j = 1:m
        C[:, m+j] .= gn[j].(θ.X) ./ θ.Y
    end    
        
    Q, R = qr(C)
	l = trues(m)	
	
	for i = 1:m
		if abs(R[m+i,m+i]) < abstol && abs(R[i,m+i]) < abstol
			l[i] = false
			# break
		end
	end
     
    θ.A = θ.A[:, l]
	θ.S = θ.S[l]	
	
	return sum(l) < m
end


function sparse_fit(θ::Basis; opt=STLSQ(exp.(-10:1:0)), abstol=1e-6, num_trials=1)  
	l = .!is_special.(expr.(θ.S))

	for i = 1:num_trials
		q₀, ϵ = sparse_fit(θ.A[:,l]; opt, abstol)

		if ϵ > abstol
			continue
		end

		q = zeros(eltype(q₀), (1,length(l)))
		q[:,l] .= q₀
		return q, ϵ
	end
	
	for i = 1:num_trials
		q, ϵ = sparse_fit(θ.A; opt, abstol)

		if ϵ > abstol
			continue
		end

		return q, ϵ
	end
	
	return nothing, Inf
end

function sparse_fit(A; opt = STLSQ(exp.(-10:1:0)), abstol = 1e-6)
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
final_result(q, θ::Basis) = final_result(q, expr.(θ.S))


############################################################################

using Combinatorics

mutable struct AnsatzFactor
	eq
	k::Int
	eqs::Array{ExprCache}
	dz::ExprCache
	X::Array{Float64}
	Y::Array{Float64}
	dY::Array{Float64}
	dZ::Array{Float64}
	ks
end

function create_ansatz_factor(eq, k, x, sub)
    D = Differential(x)    
	Iu, dz = apply_partial_int_rules(eq, x)
    U = substitute(Iu, sub)
    dU = expand_derivatives(D(eq)) / dz
    
	q = vcat(split_terms(eq), split_terms(U), split_terms(dU))

    return q
end

