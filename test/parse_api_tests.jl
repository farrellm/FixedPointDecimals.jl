using Test
using FixedPointDecimals
using FixedPointDecimals: RoundThrows

# Outcome of `parse` as a string: the backing integer, or the kind of exception thrown.
function parse_outcome(::Type{FD}, s, mode=RoundNearest) where {FD}
    try
        return string(parse(FD, s, mode).i)
    catch e
        e isa InexactError && return "Inexact"
        e isa OverflowError && return "Overflow"
        e isa ArgumentError && return "Argument"
        rethrow()
    end
end

# `tryparse` must return `nothing` exactly when `parse` throws, and agree with it otherwise.
function tryparse_agrees(::Type{FD}, s, mode=RoundNearest) where {FD}
    res = tryparse(FD, s, mode)
    out = parse_outcome(FD, s, mode)
    return isnothing(res) ? out in ("Inexact", "Overflow", "Argument") : out == string(res.i)
end

@testset "edge cases" begin
    FD2 = FixedDecimal{Int64,2}
    cases = [
        # whitespace: ASCII spaces and tabs around the number are allowed, nothing else
        " 1.5" => "150", "1.5 " => "150", "\t1.5" => "150", "1.5\t" => "150", "  1.5  " => "150",
        " " => "Argument", "\t" => "Argument", "1 .5" => "Argument", "1. 5" => "Argument",
        "\n1.5" => "Argument", "1.5\n" => "Argument", "\r1.5" => "Argument", "1.5\r" => "Argument",
        "- 1" => "Argument", "1 e2" => "Argument", "1e 2" => "Argument",
        # signs
        "+" => "Argument", "-" => "Argument", "+.5" => "50", "-.5" => "-50", "--1" => "Argument",
        "+-1" => "Argument", "-+1" => "Argument", "1-" => "Argument", "1+" => "Argument",
        # decimal marks
        "." => "Argument", ".." => "Argument", ".-" => "Argument", ".1." => "Argument",
        "1.." => "Argument", "0." => "0", "-0." => "0", "00" => "0", ".5" => "50", "5." => "500",
        # exponents
        "1E5" => "10000000", "1e+2" => "10000", "1.e2" => "10000", ".5e1" => "500", "1e01" => "1000",
        "1e-01" => "10", "1e0000000000000000000000000000000002" => "10000", "1e" => "Argument",
        "1e+" => "Argument", "1e-" => "Argument", "-.e" => "Argument", "e1" => "Argument",
        "E1" => "Argument", "1e+-1" => "Argument", "1e1.0" => "Argument", "1ee1" => "Argument",
        "1e2e3" => "Argument",
        # zeros and huge exponents
        "-0" => "0", "0e-99999" => "0", "1e-99999" => "0", "1e-9223372036854775808" => "0",
        "1e-99999999999999999999999" => "0", "1e18" => "Overflow", "1e300" => "Overflow",
        "0e300" => "0", "0.0e300" => "0",
        # leading and trailing zeros
        "0"^45 * "1.5" => "150", "0." * "0"^45 * "1" => "0", "1" * "0"^400 * "e-400" => "100",
        "1." * "0"^400 => "100", "0"^400 => "0",
        # junk
        "1,000.5" => "Argument", "1_000" => "Argument", "\0" => "Argument", "1.5\0" => "Argument",
        "\0" * "1.5" => "Argument", "é" => "Argument", "1.5é" => "Argument", "NaN" => "Argument",
        "Inf" => "Argument", "-Inf" => "Argument", "0x10" => "Argument", "0b1" => "Argument",
        "\"1.5\"" => "Argument", "1.5;" => "Argument", "1.5," => "Argument", "1.2.3" => "Argument",
        "foo" => "Argument", "1.5foo" => "Argument", "" => "Argument",
    ]
    @testset "$(repr(s))" for (s, expected) in cases
        @test parse_outcome(FD2, s) == expected
        @test tryparse_agrees(FD2, s)
    end

    @testset "rounding of tiny values" begin
        @test parse_outcome(FD2, "1e-99999", RoundToZero) == "0"
        @test parse_outcome(FD2, "1e-99999", RoundThrows) == "Inexact"
        @test parse_outcome(FD2, "0e-99999", RoundThrows) == "0"
        @test parse_outcome(FD2, "0.005") == "0"   # ties to even
        @test parse_outcome(FD2, "0.015") == "2"   # ties to even
        @test parse_outcome(FD2, "0.0050000000000000000000000001") == "1"
        @test parse_outcome(FD2, "0.0049999999999999999999999999") == "0"
        @test parse_outcome(FD2, "-0.0050000000000000000000000001") == "-1"
    end

    @testset "unsigned" begin
        U1 = FixedDecimal{UInt8,1}
        @test parse_outcome(U1, "-0") == "0"
        @test parse_outcome(U1, "-0.0") == "0"
        @test parse_outcome(U1, "-0e5") == "0"
        @test parse_outcome(U1, "-1") == "Argument"
        @test parse_outcome(U1, "-0.01") == "Argument"
        @test parse_outcome(U1, "-0.01", RoundToZero) == "Argument"
        @test parse_outcome(U1, "-0.05") == "Argument"
        @test parse_outcome(U1, "25.5") == "255"
        @test parse_outcome(U1, "25.6") == "Overflow"
        @test parse_outcome(U1, "25.54") == "255"
        @test parse_outcome(U1, "25.55") == "Overflow"
    end

    @testset "boundaries" begin
        @test parse_outcome(FixedDecimal{Int8,2}, "1.275") == "Overflow"
        @test parse_outcome(FixedDecimal{Int8,2}, "1.2749999999999999999999999999999999999999999") == "127"
        @test parse_outcome(FixedDecimal{Int8,2}, "-1.285") == "-128"
        @test parse_outcome(FixedDecimal{Int8,2}, "-1.2851") == "Overflow"
        @test parse_outcome(FixedDecimal{Int64,0}, "9223372036854775807") == "9223372036854775807"
        @test parse_outcome(FixedDecimal{Int64,0}, "9223372036854775808") == "Overflow"
        @test parse_outcome(FixedDecimal{Int64,0}, "-9223372036854775808") == "-9223372036854775808"
        @test parse_outcome(FixedDecimal{Int64,0}, "-9223372036854775809") == "Overflow"
        @test parse_outcome(FixedDecimal{UInt64,0}, "18446744073709551615") == "18446744073709551615"
        @test parse_outcome(FixedDecimal{UInt64,0}, "18446744073709551616") == "Overflow"
        @test parse_outcome(FixedDecimal{UInt128,0}, string(typemax(UInt128))) == string(typemax(UInt128))
        @test parse_outcome(FixedDecimal{UInt128,0}, string(big(typemax(UInt128)) + 1)) == "Overflow"
        @test parse_outcome(FixedDecimal{Int128,0}, string(typemin(Int128))) == string(typemin(Int128))
        @test parse_outcome(FixedDecimal{Int128,0}, string(big(typemin(Int128)) - 1)) == "Overflow"
        @test parse_outcome(FixedDecimal{Int128,38}, "1.70141183460469231731687303715884105727") == string(typemax(Int128))
        @test parse_outcome(FixedDecimal{Int128,38}, "1.70141183460469231731687303715884105728") == "Overflow"
        @test parse_outcome(FixedDecimal{Int128,38}, "-1.70141183460469231731687303715884105728") == string(typemin(Int128))
        @test parse_outcome(FixedDecimal{Int64,2}, "9"^20) == "Overflow"
        # Digits past the 39th must still take part in rounding
        @test parse_outcome(FixedDecimal{Int64,0}, "0." * "4"^40 * "9") == "0"
        @test parse_outcome(FixedDecimal{Int64,0}, "0.5" * "0"^60 * "1") == "1"
        @test parse_outcome(FixedDecimal{Int64,0}, "0.5" * "0"^60) == "0"
        @test parse_outcome(FixedDecimal{Int64,4}, "9"^60 * "e-50") == "100000000000000"
    end

    @testset "string types" begin
        @test parse(FD2, SubString("xx1.25yy", 3, 6)) == FD2(1.25)
        @test tryparse(FD2, SubString("xx1.25yy", 3, 6)) == FD2(1.25)
        @test_throws ArgumentError parse(FD2, SubString("xx1.25yy", 3, 7))  # trailing junk
        @test isnothing(tryparse(FD2, SubString("xx1.25yy", 2, 6)))         # leading junk
    end

    @testset "rounding modes" begin
        @test_throws ArgumentError parse(FD2, "1.5", RoundUp)
        @test_throws ArgumentError tryparse(FD2, "1.5", RoundDown)
        @test_throws ArgumentError parse(FD2, "1.5", RoundNearestTiesAway)
    end
end

@testset "golden corpus" begin
    path = joinpath(@__DIR__, "data", "parse_golden.tsv")
    modes = Dict("N" => RoundNearest, "Z" => RoundToZero, "T" => RoundThrows)
    types = Dict(string(T) => T for T in (Int8, UInt8, Int16, Int32, Int64, UInt64, Int128, UInt128))
    nfail = 0
    ncases = 0
    for line in eachline(path)
        startswith(line, '#') && continue
        tstr, fstr, mstr, input, expected = split(line, '\t')
        FD = FixedDecimal{types[tstr], parse(Int, fstr)}
        s = unescape_string(input)
        mode = modes[mstr]
        ncases += 1
        got = parse_outcome(FD, s, mode)
        ok = got == expected && tryparse_agrees(FD, s, mode)
        if !ok
            nfail += 1
            nfail <= 20 && @error "golden mismatch" FD s mode expected got
        end
    end
    @test ncases > 20_000
    @test nfail == 0
end
