module CSA
using Nemo
using Singular

struct CentralSimpleAlgebra{T <: Nemo.RingElem}
    
    ring:: LPRing{T}
    ideal:: sideal{slpalg{T}}
    degree:: Int

    function CentralSimpleAlgebra(R:: LPRing{T}, I:: sideal{slpalg{T}}, degree::Int) where T<: Nemo.RingElem
        new{T}(R,I, degree)
    end

end

function SymbolAlgebra(a:: Nemo.FieldElem, b::Nemo.FieldElem, u::Nemo.FieldElem, degree::Int)
    
    parent(a) != parent(b) && error("Symbols must be from same field")
    parent(u) != parent(a) && error("Root of unity not from same field as symbols")
    u^degree != one(parent(a)) && error("No root of unity provided")

    F=parent(a)

    R, (x,y) = FreeAlgebra(F, ["x", "y"], 2*degree)
    I=std(Ideal(R, [x^degree-a, y^degree-b, x*y-u*y*x]))

    return CentralSimpleAlgebra(R, I, degree)

end

function symbol_algebra(a:: Nemo.FieldElem, b::Nemo.FieldElem, u::Nemo.FieldElem, degree::Int)
    
    parent(a) != parent(b) && error("Symbols must be from same field")
    parent(u) != parent(a) && error("Root of unity not from same field as symbols")
    u^degree != one(parent(a)) && error("No root of unity provided")

    F=parent(a)

    R, (x,y) = FreeAlgebra(F, ["x", "y"], 2*degree)
    I=std(Ideal(R, [x^degree-a, y^degree-b, x*y-u*y*x]))

    return CentralSimpleAlgebra(R, I, degree)

end

function tensor_product(A:: CentralSimpleAlgebra{T}, B:: CentralSimpleAlgebra{T}) where T <: Nemo.FieldElem
    
    base_ring(A.ring) != base_ring(B.ring) && error("Algebras must be defined over common base field")

    n=length(gens(A.ring))
    m=length(gens(B.ring))

    base = base_ring(A.ring)

    tensor_gens=["x$i" for i in (1:n+m)]

    R, x = FreeAlgebra(base, tensor_gens, 2*(A.degree*B.degree))

    tensor_ideal = typeof(x[1])[ ]

    for i in (1:number_of_generators(A.ideal))
        coeffs = collect(coefficients(A.ideal[i]))
        exps = collect(Singular.exponent_words(A.ideal[i]))

        b = MPolyBuildCtx(R)

        for j in eachindex(coeffs)
            push_term!(b, base(coeffs[j]), exps[j])
        end

        push!(tensor_ideal, finish(b))

    end

    for i in (1:number_of_generators(B.ideal))
        coeffs = collect(coefficients(B.ideal[i]))
        exps = collect(Singular.exponent_words(B.ideal[i]))

        b = MPolyBuildCtx(R)

        for j in eachindex(coeffs)
            push_term!(b, base(coeffs[j]), exps[j].+n)
        end

        push!(tensor_ideal, finish(b))

    end

    for i in (1:n)
        for j in (1:m)
           push!(tensor_ideal, x[i]*x[n+j]-x[n+j]*x[i]) 
        end
    end

    J=std(Ideal(R, tensor_ideal))

    return CentralSimpleAlgebra(R, J, A.degree*B.degree)

end

end # module CSAs
