using Chairmarks, Graphs, Random, SoleLogics, StatsBase, ThreadSafeDicts
using SoleLogics: AbstractKripkeStructure, AbstractSyntaxBranch, AnyWorld, World
using SoleLogics: allworlds, collateworlds, frame, isgrounded
import SoleLogics: check

function generatemodalformulas(n::Int, h::Int; seed::Int=42)
    rng = Xoshiro(seed)
    Σ = Atom.(["p","q","r","s","t"])
    os = Vector{Connective}([∧, ∨, →, ¬, ◊, □])

    aot = vcat(Σ, [⊤, ⊥])
    aotpicker = (rng)->StatsBase.sample(rng, aot, uweights(length(aot)))

    Γ = Vector{Union{Atom, BooleanTruth, SyntaxBranch}}()
    for _ in 1:n
        push!(
            Γ, 
            randformula(
                rng,
                h,
                Σ,
                os,
                opweights = StatsBase.uweights(length(os)),
                basecase = aotpicker,
                mode = :full
            )
        )
    end
    return Γ
end

function generatemodalmodels(n::Int, nw::Int, ne::Int; seed::Int=42)
    rng = Xoshiro(seed)
    Σ = Atom.(["p","q","r","s","t"])
    e = Vector{KripkeStructure}()
    for _ in 1:n
        g = SimpleDiGraph(nw,ne)
        rem_vertices!(g, vertices(g)[map(v->!has_path(g,1,v),vertices(g))])
        f = SoleLogics.ExplicitCrispUniModalFrame(SoleLogics.World.(1:nv(g)), g)
        v = Dict{
            SoleLogics.World{Int64},
            TruthDict{Dict{Atom{String}, BooleanTruth}}
        }()
        ws = f.worlds
        for i in 1:length(f.worlds)
            v[ws[i]] = TruthDict{Dict{Atom{String}, BooleanTruth}}()
            values = bitrand(rng, 5)
            for j in 1:5
                v[ws[i]][Σ[j]] = values[j]
            end
        end
        push!(e, KripkeStructure(f, v))
    end
    return e
end

function check(
    Γ::Vector{Union{Atom, BooleanTruth, SyntaxBranch}},
    e::Vector{KripkeStructure}
)
    for φ ∈ Γ
        for m ∈ e
            check(φ, m, AnyWorld())
        end
    end
end

Γ = generatemodalformulas(50, 7);
e = generatemodalmodels(50, 7, 18);
println(@b check(Γ, e))

################################################################################
# SoleLogics stable
# Sample(
#     time=2.754634035,
#     allocs=31954174,
#     bytes=1066752816,
#     gc_fraction=0.041466784534229424
# )
# SoleLogics optimized
# Sample(
    # time=0.7970670470000001,
    # allocs=22544380,
    # bytes=609228912,
    # gc_fraction=0.07724754928928833,
    # compile_fraction=0.0022924043929268096,
    # recompile_fraction=1.0
# )
################################################################################
