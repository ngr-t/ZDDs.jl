using ZDDs
using Test
import Random

# Helper: canonical Set{Set{Int}} representation of a family of iterables.
normfam(family) = Set(Set(Int.(s)) for s in family)

@testset "ZDDs.jl" begin

    @testset "README examples" begin
        zdd1 = tozdd(((1,), (1, 2)))
        zdd2 = tozdd(((2,), (1, 2), (2, 3, 4)))

        @test tofamily(union(zdd1, zdd2)) ==
            normfam([[1], [2], [1, 2], [2, 3, 4]])
        @test tofamily(setdiff(zdd1, zdd2)) == normfam([[1]])
        @test tofamily(setdiff(zdd2, zdd1)) == normfam([[2], [2, 3, 4]])
        @test tofamily(intersect(zdd1, zdd2)) == normfam([[1, 2]])
    end

    @testset "tozdd / tofamily roundtrip" begin
        for fam in (Vector{Int}[], [Int[]], [[1]], [[1, 2], [2, 3], [3]],
                    [[5], [6, 5], [4, 1]])
            @test tofamily(tozdd(fam)) == normfam(fam)
        end
        # empty family vs base family {∅}
        @test tofamily(tozdd(Vector{Int}[])) == Set{Set{Int}}()
        @test tofamily(tozdd([Int[]])) == Set([Set{Int}()])
    end

    @testset "length" begin
        @test length(tozdd(Vector{Int}[])) == 0
        @test length(tozdd([Int[]])) == 1
        @test length(tozdd([[1, 2], [2, 3], [3]])) == 3
    end

    @testset "deduplication (regression)" begin
        # Duplicate sets, unsorted input, and repeated elements must collapse.
        @test length(tozdd([[1, 3], [1, 3]])) == 1
        @test length(tozdd([Int[], Int[]])) == 1
        @test tofamily(tozdd([[3, 1], [1, 3]])) == normfam([[1, 3]])
        @test tofamily(tozdd([[1, 1, 2], [2, 1]])) == normfam([[1, 2]])
    end

    @testset "subset0 / subset1 / change" begin
        z = tozdd([[1, 2], [2, 3], [3]])
        @test tofamily(subset1(z, 2)) == normfam([[1], [3]])
        @test tofamily(subset0(z, 2)) == normfam([[3]])
        @test tofamily(change(z, 2)) == normfam([[1], [3], [2, 3]])
    end

    @testset "unary ops below minimum element (regression)" begin
        # These used to StackOverflow because the descent reached a terminal
        # node whose magic *top* value never satisfied the base case.
        z = tozdd([[2]])
        @test tofamily(subset1(z, 1)) == Set{Set{Int}}()
        @test tofamily(subset0(z, 1)) == normfam([[2]])
        @test tofamily(change(z, 1)) == normfam([[1, 2]])

        # change on empty / base families
        @test tofamily(change(tozdd(Vector{Int}[]), 1)) == Set{Set{Int}}()
        @test tofamily(change(tozdd([Int[]]), 1)) == normfam([[1]])
    end

    @testset "set operations vs brute force" begin
        Random.seed!(20240625)
        mk() = begin
            f = Vector{Vector{Int}}()
            for _ in 1:rand(0:6)
                push!(f, rand(1:7, rand(0:5)))
            end
            f
        end
        for _ in 1:500
            fa, fb = mk(), mk()
            A, B = normfam(fa), normfam(fb)
            za, zb = tozdd(fa), tozdd(fb)
            @test tofamily(union(za, zb)) == union(A, B)
            @test tofamily(intersect(za, zb)) == intersect(A, B)
            @test tofamily(setdiff(za, zb)) == setdiff(A, B)
            @test length(za) == length(A)
        end
    end

    @testset "operation cache (power-set, perf regression)" begin
        # Build the power-set ZDD of {1..50}. The ZDD has only ~50 nodes, but
        # it represents 2^50 combinations. Without the operation cache, both the
        # repeated *union*/*change* construction and *length* would each take
        # time proportional to 2^50 recursive calls and never finish. With the
        # computed table this is instant. This both demonstrates and guards the
        # memoization fix.
        p = tozdd([Int[]])
        for i in 1:50
            p = union(p, change(p, i))
        end
        @test length(p) == 2^50  # 1125899906842624
    end

end
