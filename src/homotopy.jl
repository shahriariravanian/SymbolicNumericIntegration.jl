transformer(eq) = transformer(ops(eq)...)

function transformer(::Mul, eq)
    return vcat([transformer(t) for t in arguments(eq)]...)
end

function transformer(::Div, eq)
    a = transformer(arguments(eq)[1])
    b = transformer(arguments(eq)[2])
    b = [(1 / q, k) for (q, k) in b]
    return [a; b]
end

function transformer(::Pow, eq)
    y, k = arguments(eq)
    if is_number(k)
        r = nice_parameter(k)
        if r isa Integer || r isa Rational
            if denominator(r) == 1
                return [(y, k)]
            else
                return [(y^(1 / denominator(r)), numerator(r))]
            end
        end
    end
    return [(eq, 1)]
end

function transformer(::Any, eq)
    return [(eq, 1)]
end

function transform(eq, x)
    p = transformer(eq)
    p = p[isdependent.(first.(p), x)]
    return p
end

@syms u[20]

function rename_factors(p, ab = ())
    n = length(p)
    q = 1
    ks = Int[]
    sub = Dict()

    for (a, b) in ab
        sub[a] = b
    end

    for (i, (y, k)) in enumerate(p)
        μ = u[i]
        q *= μ^k
        sub[μ] = y
        push!(ks, k)
    end

    return q, sub, ks
end

##############################################################################

Symbolics.@register_symbolic Ei(z)
Symbolics.@register_symbolic Si(z)
Symbolics.@register_symbolic Ci(z)
Symbolics.@register_symbolic Li(z)

Symbolics.derivative(::typeof(Ei), args::NTuple{1, Any}, ::Val{1}) = exp(args[1]) / args[1]
Symbolics.derivative(::typeof(Si), args::NTuple{1, Any}, ::Val{1}) = sin(args[1]) / args[1]
Symbolics.derivative(::typeof(Ci), args::NTuple{1, Any}, ::Val{1}) = cos(args[1]) / args[1]
Symbolics.derivative(::typeof(Li), args::NTuple{1, Any}, ::Val{1}) = 1 / log(args[1])

@syms 𝑥 si(𝑥) ci(𝑥) ei(𝑥) li(𝑥)

##############################################################################

guard_zero(x) = isequal(x, 0) ? one(x) : x

function generate_homotopy(eq, x)
    eq = eq isa Num ? eq.val : eq
    x = x isa Num ? x.val : x

    p = transform(eq, x)
    q, sub, ks = rename_factors(p, (si => Si, ci => Ci, ei => Ei, li => Li))
    S = 0

    for i in 1:length(ks)
        μ = u[i]
        h₁, ∂h₁ = apply_partial_int_rules(sub[μ], x)
        h₁ = substitute(h₁, sub)

        for j in 1:ks[i]
            h₂ = substitute((q / μ^j) / ∂h₁, sub)
            S += expand((ω + h₁) * (ω + h₂))
        end
    end

    S = substitute(S, Dict(ω => 1))
    unique([x; [equivalent(t, x) for t in terms(S)]])
end

########################## Main Integration Rules ##################################

@syms 𝛷(x)

partial_int_rules = [
                     # trigonometric functions
                     @rule 𝛷(sin(~x)) => (cos(~x) + si(~x), ~x)                     
                     # @rule 𝛷(sin(~x)) => (cos(~x), ~x)                     
                     @rule 𝛷(cos(~x)) => (sin(~x) + ci(~x), ~x)
                     @rule 𝛷(tan(~x)) => (1 + log(cos(~x)), ~x)
                     @rule 𝛷(csc(~x)) => (1 + log(csc(~x) + cot(~x)) + log(sin(~x)), ~x)
                     @rule 𝛷(sec(~x)) => (1 + log(sec(~x) + tan(~x)) + log(cos(~x)), ~x)
                     @rule 𝛷(cot(~x)) => (1 + log(sin(~x)), ~x)
                     # hyperbolic functions
                     @rule 𝛷(sinh(~x)) => (cosh(~x), ~x)
                     @rule 𝛷(cosh(~x)) => (sinh(~x), ~x)
                     @rule 𝛷(tanh(~x)) => (1 + log(cosh(~x)), ~x)
                     @rule 𝛷(csch(~x)) => (1 + log(tanh(~x / 2)), ~x)
                     @rule 𝛷(sech(~x)) => (atan(sinh(~x)), ~x)
                     @rule 𝛷(coth(~x)) => (1 + log(sinh(~x)), ~x)
                     # 1/trigonometric functions
                     @rule 𝛷(1 / sin(~x)) => (1 + log(csc(~x) + cot(~x)) + log(sin(~x)), ~x)
                     @rule 𝛷(1 / cos(~x)) => (1 + log(sec(~x) + tan(~x)) + log(cos(~x)), ~x)
                     @rule 𝛷(1 / tan(~x)) => (1 + log(sin(~x)) + log(tan(~x)), ~x)
                     @rule 𝛷(1 / csc(~x)) => (cos(~x) + log(csc(~x)), ~x)
                     @rule 𝛷(1 / sec(~x)) => (sin(~x) + log(sec(~x)), ~x)
                     @rule 𝛷(1 / cot(~x)) => (1 + log(cos(~x)) + log(cot(~x)), ~x)
                     # 1/hyperbolic functions
                     @rule 𝛷(1 / sinh(~x)) => (log(tanh(~x / 2)) + log(sinh(~x)), ~x)
                     @rule 𝛷(1 / cosh(~x)) => (atan(sinh(~x)) + log(cosh(~x)), ~x)
                     @rule 𝛷(1 / tanh(~x)) => (1 + log(sinh(~x)) + log(tanh(~x)), ~x)
                     @rule 𝛷(1 / csch(~x)) => (cosh(~x) + log(csch(~x)), ~x)
                     @rule 𝛷(1 / sech(~x)) => (sinh(~x) + log(sech(~x)), ~x)
                     @rule 𝛷(1 / coth(~x)) => (1 + log(cosh(~x)) + log(coth(~x)), ~x)
                     # inverse trigonometric functions
                     @rule 𝛷(asin(~x)) => (~x * asin(~x) + sqrt(1 - ~x * ~x), ~x)
                     @rule 𝛷(acos(~x)) => (~x * acos(~x) + sqrt(1 - ~x * ~x), ~x)
                     @rule 𝛷(atan(~x)) => (1 + ~x * atan(~x) + log(~x * ~x + 1), ~x)
                     @rule 𝛷(acsc(~x)) => (~x * acsc(~x) + atanh(1 - ^(~x, -2)), ~x)
                     @rule 𝛷(asec(~x)) => (~x * asec(~x) + acosh(~x), ~x)
                     @rule 𝛷(acot(~x)) => (1 + ~x * acot(~x) + log(~x * ~x + 1), ~x)
                     # inverse hyperbolic functions
                     @rule 𝛷(asinh(~x)) => (~x * asinh(~x) + sqrt(~x * ~x + 1), ~x)
                     @rule 𝛷(acosh(~x)) => (~x * acosh(~x) + sqrt(~x * ~x - 1), ~x)
                     @rule 𝛷(atanh(~x)) => (~x * atanh(~x) + log(~x + 1), ~x)
                     @rule 𝛷(acsch(~x)) => (acsch(~x), ~x)
                     @rule 𝛷(asech(~x)) => (asech(~x), ~x)
                     @rule 𝛷(acoth(~x)) => (~x * acot(~x) + log(~x + 1), ~x)
                     # logarithmic and exponential functions
                     @rule 𝛷(log(~x)) => (1 + ~x + ~x * log(~x) +
                                          sum(candidate_pow_minus(~x, -1); init = one(~x)),
                                          ~x)
                     @rule 𝛷(1 / log(~x)) => (1 + log(log(~x)) + li(~x), ~x)
                     @rule 𝛷(exp(~x)) => (exp(~x) + ei(~x), ~x)
                     @rule 𝛷(^(exp(~x), ~k::is_neg)) => (^(exp(-~x), -~k), ~x)
                     # square-root functions
                     @rule 𝛷(^(~x, ~k::is_abs_half)) => (sum(candidate_sqrt(~x, ~k);
                                                             init = one(~x)), ~x);
                     @rule 𝛷(sqrt(~x)) => (sum(candidate_sqrt(~x, 0.5); init = one(~x)), ~x);
                     @rule 𝛷(1 / sqrt(~x)) => (sum(candidate_sqrt(~x, -0.5);
                                                   init = one(~x)), ~x);
                     # rational functions                                                              
                     @rule 𝛷(1 / ^(~x::is_poly, ~k::is_pos_int)) => (sum(candidate_pow_minus(~x,
                                                                                             -~k);
                                                                         init = one(~x)),
                                                                     ~x)
                     @rule 𝛷(1 / ~x::is_poly) => (sum(candidate_pow_minus(~x, -1);
                                                      init = one(~x)), ~x);
                     @rule 𝛷(^(~x, -1)) => (1 + log(~x), ~x)
                     @rule 𝛷(^(~x, ~k::is_neg_int)) => (sum(^(~x, i) for i in (~k + 1):-1),
                                                        ~x)
                     @rule 𝛷(1 / ~x) => (log(~x), ~x)
                     @rule 𝛷(^(~x, ~k::is_pos_int)) => (sum(^(~x, i + 1)
                                                            for i in 1:(~k + 1)),
                                                        ~x)
                     @rule 𝛷(1) => (𝑥, 1)
                     @rule 𝛷(~x) => ((~x + ^(~x, 2)), ~x)]

function apply_partial_int_rules(eq, x)
    y, dy = expand(Fixpoint(Prewalk(Chain(partial_int_rules))))(𝛷(value(eq)))
    D = Differential(x)
    return y, guard_zero(expand_derivatives(D(dy)))
end
