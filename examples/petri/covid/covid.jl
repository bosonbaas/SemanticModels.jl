using Catlab
using Catlab.Doctrines
using Catlab.Graphics
using Catlab.WiringDiagrams
using Catlab.Programs
import Base.Multimedia: display
import Catlab.Graphics: to_graphviz, LeftToRight

import Catlab.Doctrines:
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, otimes, ⊗, ⊕, munit, mzero, braid,
  dagger, dunit, dcounit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  plus, zero, coplus, cozero, meet, top, join, bottom

wd = to_wiring_diagram
draw(d::WiringDiagram) = to_graphviz(add_junctions(d), orientation=LeftToRight, labels=true)
draw(d::HomExpr) = draw(wd(d))

@theory BiproductCategory(Ob, Hom) => Epidemiology(Ob, Hom) begin
    spontaneous(A::Ob, B::Ob)::Hom(A,B)
    transmission(A::Ob, B::Ob)::Hom(A⊗B, B⊗B)
    exposure(A::Ob, B::Ob, C::Ob)::Hom(A⊗B, C⊗B)
    death(A)::Hom(A, munit()) ⊣ A::Ob
end

spontaneous(A::Ports, B::Ports) = singleton_diagram(Epidemiology.Hom, Box(:→, A, B))
exposure(A::Ports, B::Ports, C::Ports) = singleton_diagram(Epidemiology.Hom, Box(:exposure, A⊗B, C⊗B))
death(A::Ports) = singleton_diagram(Epidemiology.Hom, Box(:𝗫, A, Ports([])))
mcopy(A::Ports{Epidemiology.Hom}, Symbol) = implicit_mcopy(A, 2)
mmerge(A::Ports{Epidemiology.Hom}, Symbol) = implicit_mmerge(A, 2)


@syntax FreeEpidemiology(ObExpr, HomExpr) Epidemiology begin
    otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
    otimes(f::Hom, g::Hom) = associate(new(f,g))
    compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))

    pair(f::Hom, g::Hom) = Δ(dom(f)) → (f ⊗ g)
    copair(f::Hom, g::Hom) = (f ⊗ g) → ∇(codom(f))
    proj1(A::Ob, B::Ob) = id(A) ⊗ ◊(B)
    proj2(A::Ob, B::Ob) = ◊(A) ⊗ id(B)
    incl1(A::Ob, B::Ob) = id(A) ⊗ □(B)
    incl2(A::Ob, B::Ob) = □(A) ⊗ id(B)
    otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
    otimes(f::Hom, g::Hom) = associate(new(f,g))
end

@present Disease(FreeEpidemiology) begin
    S::Ob
    E::Ob
    I::Ob
    R::Ob
end

S,E,I,R = generators(Disease)
draw(spontaneous(E,I)⋅spontaneous(I,R)⊗(spontaneous(E,I)))
sei = compose(exposure(S,I,E), otimes(spontaneous(E,I), id(I)), mmerge(I))
draw(sei)
seir = sei⋅Δ(I)⋅(id(I)⊗spontaneous(I, R))
draw(seir)
seir2 = compose(mcopy(S)⊗id(I), id(S)⊗seir)
draw(seir2)

draw(death(S))

d = @program Disease (s::S, e::E, i::I) begin
    e1, i1 = exposure{S,I,E}(s,i)
    i2 = spontaneous{E,I}(e1)
    e = [e, e1]
    e_out = spontaneous{E,E}(e)
    i1 = [i1, i2]
    r = spontaneous{I,R}(i1)
    s_out = spontaneous{S,S}(s)
    return s_out, e_out, spontaneous{I,I}(i1)
end
draw(d)

draw(d⋅d)

seirdef = to_hom_expr(FreeEpidemiology, d)
try
    add_definition!(Disease, :seir, seirdef)
catch
    println("INFO: definition already added.")
end

# if the disease is fatal, we need to add a death component
seird = @program Disease (s::S, e::E, i::I) begin
    e1, i1 = exposure{S,I,E}(s,i)
    i2 = spontaneous{E,I}(e1)
    e = [e, e1]
    e_out = spontaneous{E,E}(e)
    i1 = [i1, i2]
    r = spontaneous{I,R}(i1)
    s_out = spontaneous{S,S}(s)
    death{I}(i1)
    return s_out, e_out, spontaneous{I,I}(i1)
end
#TODO: This does not get translated correctly, bug?
seirddef = to_hom_expr(FreeEpidemiology, seird)
try
    add_definition!(Disease, :seird, seirddef)
catch
    println("INFO: definition already added.")
end

seirgen = generator(Disease, :seir)
seirdgen = generator(Disease, :seird)


ncities(city,n::Int) = compose([city for i in 1:n]...)
city³ = ncities(seirgen, 3)
draw(city³)

dcity³ = wd(city³)
dc3 = substitute(dcity³, box_ids(dcity³), [d,d,d])
@show dc3 == ncities(d, 3)
draw(dc3)

import Base: repeat
repeat(d::WiringDiagram, n::Int) = compose([d for i in 1:n]...)
repeat(d::FreeEpidemiology.Hom, n::Int) = compose([d for i in 1:n]...)

draw(ncities(seirdgen, 3))
draw(repeat(seird, 3))

draw(seirddef)
#
# using TikzPictures
# using Catlab.Graphics.TikZWiringDiagrams
# using Convex
# using SCS
#
# to_tikz(seirddef, labels=true)
