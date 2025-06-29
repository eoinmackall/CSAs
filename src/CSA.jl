module CSA
using Oscar
import Base: +, -, *, ^, ==, deepcopy_internal, hash, one, parent, show, zero

#Structs for CentralSimpleAlgebra's and CentralSimpleAlgebraElem's
mutable struct CentralSimpleAlgebra{T} <: NCRing
    base_ring:: Field
    ring:: FreeAssociativeAlgebra{T}
    ideal:: Oscar.FreeAssociativeAlgebraIdeal{AbstractAlgebra.Generic.FreeAssociativeAlgebraElem{T}}
    degree::Int

    function CentralSimpleAlgebra(base_ring::Field, R::FreeAssociativeAlgebra{T}, I::Oscar.FreeAssociativeAlgebraIdeal{AbstractAlgebra.Generic.FreeAssociativeAlgebraElem{T}}, degree:: Int) where T
        new{T}(base_ring, R,I,degree)
    end
end

mutable struct CentralSimpleAlgebraElem{T} <: NCRingElem
    parent:: CentralSimpleAlgebra{T}
    data::FreeAssociativeAlgebraElem{T}
end


#TODO incoporate the normal_form into arithmetic of CentralSimpleAlgebraElem's
#Functions required for using the NCRing interface
parent_type(::Type{CentralSimpleAlgebraElem{T}}) where T = CentralSimpleAlgebra{T}
elem_type(::Type{CentralSimpleAlgebra{T}}) where T = CentralSimpleAlgebraElem{T}
base_ring_type(::Type{CentralSimpleAlgebra{T}}) where T = parent_type(T)
base_ring(R::CentralSimpleAlgebra{T}) where T = R.base_ring
parent(f::CentralSimpleAlgebraElem{T}) where T = f.parent
is_domain_type(::Type{CentralSimpleAlgebraElem{T}}) where T = false
is_exact_type(::Type{CentralSimpleAlgebraElem{T}}) where T = is_exact_type(T)

function Base.deepcopy_internal(a:: CentralSimpleAlgebraElem, dict:: IdDict)
    return CentralSimpleAlgebraElem(parent(a), deepcopy_internal(a.data, dict))
end

function Base.hash(a:: CentralSimpleAlgebraElem, h::UInt)
    return hash(a.data, h)
end

function Base.show(io::IO, R::CentralSimpleAlgebra{T}) where T
    Oscar.@show_special(io, R)
    print(io, "Central Simple Algebra over ", R.base_ring, " of degree ", R.degree)    
end

function Base.show(io::IO, a::CentralSimpleAlgebraElem)
    Oscar.@show_special(io, a)
    print(io, "element of ", a.parent)
end

function Base.:(==)(a::CentralSimpleAlgebraElem, b::CentralSimpleAlgebraElem)
    return is_zero(a - b)
end

function Base.:+(a::CentralSimpleAlgebraElem, b::CentralSimpleAlgebraElem)
    check_parent(a,b)
    return CentralSimpleAlgebraElem(parent(a), a.data + b.data)
end

function Base.:-(a::CentralSimpleAlgebraElem, b::CentralSimpleAlgebraElem)
    check_parent(a,b)
    return CentralSimpleAlgebraElem(parent(a), a.data - b.data)
end

function Base.:*(a::CentralSimpleAlgebraElem, b::CentralSimpleAlgebraElem)
    check_parent(a,b)
    return CentralSimpleAlgebraElem(parent(a), a.data*b.data)
end

function Base.:^(a::CentralSimpleAlgebraElem, b::Int)
     b >= 0 || DomainError("Implementation not made for negative exponents yet") 
    return CentralSimpleAlgebraElem(parent(a), a.data^b)
end

function divexact_left(a::CentralSimpleAlgebraElem, b::CentralSimpleAlgebraElem)
    check_parent(a,b)
    is_unit(b) || throw(DomainError(b, "is not a unit"))
    throw(NotImplementedError(divexact_left, a))
end

function divexact_right(a::CentralSimpleAlgebraElem, b::CentralSimpleAlgebraElem)
    check_parent(a,b)
    is_unit(b) || throw(DomainError(b, "is not a unit"))
    throw(NotImplementedError(divexact_right, a))
end

function (R:: CentralSimpleAlgebra)()
    return CentralSimpleAlgebraElem(R, R.base_ring())
end

function (R:: CentralSimpleAlgebra)(a::Integer)
    return CentralSimpleAlgebraElem(R, R.base_ring(a))
end

function (R:: CentralSimpleAlgebra)(a:: CentralSimpleAlgebraElem)
    check_parent(a,R()) || error("element does not belong to algebra provided")
    return a
end

function (R::CentralSimpleAlgebra{T})(a::T) where T <: RingElem
    check_parent(a, R.base_ring()) || error("parent ring of element differs from base ring of algebra")
    return CentralSimpleAlgebraElem(R, R.ring(a))
end

function zero(R:: CentralSimpleAlgebra)
    return CentralSimpleAlgebraElem(R, R.ring(0))
end

function one(R:: CentralSimpleAlgebra)
    return CentralSimpleAlgebraElem(R, R.ring(1))
end

function iszero(a::CentralSimpleAlgebraElem)
    ideal_membership(a.data, a.parent.ideal)
end

function isone(a::CentralSimpleAlgebraElem)
    return a==a.parent(1)
end

function isunit(a::CentralSimpleAlgebraElem)
    is_unit(a.data) && return true
    is_zero(a.data) && return false
    throw(NotImplementedError(:is_unit, a))
    #TODO add reduced norm implementation  
end

function canonical_unit(a::CentralSimpleAlgebraElem)
    return a.parent(1) #TODO implementation not yet made
end




#SymbolAlgebra constructors/functionality
function SymbolAlgebra(a:: FieldElem, b::FieldElem, u::FieldElem, degree::Int)
    
    check_parent(a,b)
    check_parent(a,u)
    u^degree != one(parent(a)) && error("No root of unity provided")

    F=parent(a)

    R, (x,y) = free_associative_algebra(F, [:x, :y])
    I=ideal(R, [x^degree-a, y^degree-b, x*y-u*y*x])

    return CentralSimpleAlgebra(F, R, I, degree)

end

function symbol_algebra(a:: FieldElem, b::FieldElem, u::FieldElem, degree::Int)
    
        
    check_parent(a,b)
    check_parent(a,u)
    u^degree != one(parent(a)) && error("No root of unity provided")

    F=parent(a)

    R, (x,y) = free_associative_algebra(F, [:x, :y])
    I=ideal(R, [x^degree-a, y^degree-b, x*y-u*y*x])

    return CentralSimpleAlgebra(F, R, I, degree)

end



# function tensor_product(A:: CentralSimpleAlgebra{T}, B:: CentralSimpleAlgebra{T}) where T <: Nemo.FieldElem
    
#     base_ring(A.ring) != base_ring(B.ring) && error("Algebras must be defined over common base field")

#     n=length(gens(A.ring))
#     m=length(gens(B.ring))

#     base = base_ring(A.ring)

#     tensor_gens=["x$i" for i in (1:n+m)]

#     R, x = FreeAlgebra(base, tensor_gens, 2*(A.degree*B.degree))

#     tensor_ideal = typeof(x[1])[ ]

#     for i in (1:number_of_generators(A.ideal))
#         coeffs = collect(coefficients(A.ideal[i]))
#         exps = collect(Singular.exponent_words(A.ideal[i]))

#         b = MPolyBuildCtx(R)

#         for j in eachindex(coeffs)
#             push_term!(b, base(coeffs[j]), exps[j])
#         end

#         push!(tensor_ideal, finish(b))

#     end

#     for i in (1:number_of_generators(B.ideal))
#         coeffs = collect(coefficients(B.ideal[i]))
#         exps = collect(Singular.exponent_words(B.ideal[i]))

#         b = MPolyBuildCtx(R)

#         for j in eachindex(coeffs)
#             push_term!(b, base(coeffs[j]), exps[j].+n)
#         end

#         push!(tensor_ideal, finish(b))

#     end

#     for i in (1:n)
#         for j in (1:m)
#         push!(tensor_ideal, x[i]*x[n+j]-x[n+j]*x[i]) 
#         end
#     end

#     J=std(Ideal(R, tensor_ideal))

#     return CentralSimpleAlgebra(R, J, A.degree*B.degree)

# end

end # module CSAs
