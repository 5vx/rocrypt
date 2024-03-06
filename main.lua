--[[
RoCrypt
----------------------------------------------------------------------------------------
DESCRIPTION:
	This module contains functions to calculate SHA digest
	    SHA-256, SHA-512
	Cyclic redundancy checks (CRC) algorithms
        CRC32
    And asymmetric algorithms
        RSA
	Written in pure Lua.
USAGE:
	Input data should be a string
	Result (SHA digest) is returned in hexadecimal representation as a string of lowercase hex digits.
	Simplest usage example:
		local RoCrypt = require(script.RoCrypt)
		local hash = RoCrypt.sha256("string here")
	SHA2 hash functions:
		RoCrypt.sha256
		RoCrypt.sha512
		RoCrypt.crc32
		RoCrypt.rsa
----------------------------------------------------------------------------------------
CREDIT: RobloxGamerPro200007 - RSA function
--]]--

RoCrypt = {}
band, bxor, bnot, rrotate, rshift, bor, lrotate, lshift = bit32.band, bit32.bxor, bit32.bnot, bit32.rrotate, bit32.rshift, bit32.bor, bit32.lrotate, bit32.lshift
char, rep, sub, format = string.char, string.rep, string.sub, string.format

function RoCrypt.sha256(message: string)

    local K = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    }

    local H = {
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    }

    local function preprocess(message)
        local len = #message
        local padding_len = 64 - ((len + 9) % 64)
        local padded_message = message.."\128"..string.rep("\0", padding_len)..string.pack(">I8", len * 8)
        return padded_message
    end

    local function processBlock(block, state)
        local W = {}
        for i = 1, 16 do
            W[i] = string.unpack(">I4", block, (i - 1) * 4 + 1)
        end
        for i = 17, 64 do
            local s0 = bxor(rrotate(W[i - 15], 7), rrotate(W[i - 15], 18), rshift(W[i - 15], 3))
            local s1 = bxor(rrotate(W[i - 2], 17), rrotate(W[i - 2], 19), rshift(W[i - 2], 10))
            W[i] = (W[i - 16] + s0 + W[i - 7] + s1) % 2^32
        end
        local a, b, c, d, e, f, g, h = unpack(state)
        for i = 1, 64 do
            local S1 = bxor(rrotate(e, 6), rrotate(e, 11), rrotate(e, 25))
            local ch = bxor(band(e, f), band(bnot(e), g))
            local temp1 = (h + S1 + ch + K[i] + W[i]) % 2^32
            local S0 = bxor(rrotate(a, 2), rrotate(a, 13), rrotate(a, 22))
            local maj = bxor(band(a, b), band(a, c), band(b, c))
            local temp2 = (S0 + maj) % 2^32
            h, g, f, e, d, c, b, a = g, f, e, (d + temp1) % 2^32, c, b, a, (temp1 + temp2) % 2^32
        end
        state[1] = (state[1] + a) % 2^32
        state[2] = (state[2] + b) % 2^32
        state[3] = (state[3] + c) % 2^32
        state[4] = (state[4] + d) % 2^32
        state[5] = (state[5] + e) % 2^32
        state[6] = (state[6] + f) % 2^32
        state[7] = (state[7] + g) % 2^32
        state[8] = (state[8] + h) % 2^32
    end


    local padded_message = preprocess(message)
    local state = {unpack(H)}
    for i = 1, #padded_message, 64 do
        local block = padded_message:sub(i, i + 63)
        processBlock(block, state)
    end
    local digest = ""
    for i = 1, 8 do
        digest = digest..string.format("%08x", state[i])
    end
    return digest
end



function RoCrypt.crc32(message: string, hex: boolean?)
    local crc = 0xFFFFFFFF
    local polynomial = 0xEDB88320

    for i = 1, #message do
        local byte = string.byte(message, i)
        crc = bxor(crc, byte)

        for _ = 1, 8 do
            local mask = -band(crc, 1)
            crc = bxor(rshift(crc, 1), band(polynomial, mask))
        end
    end
        if hex == true then
        return string.format("%X", bxor(crc, 0xFFFFFFFF))
    elseif not hex or hex == false then
        return bxor(crc, 0xFFFFFFFF)
    end
end

function RoCrypt.rsa()
    local primes = {	3,    5,    7,   11,   13,   17,   19,   23,   29,   31,   37,   41,   43,   47,
        53,   59,   61,   67,   71,   73,   79,   83,   89,   97,  101,  103,  107,  109,  113,  127,
        131,  137,  139,  149,  151,  157,  163,  167,  173,  179,  181,  191,  193,  197,  199,  211,
        223,  227,  229,  233,  239,  241,  251,  257,  263,  269,  271,  277,  281,  283,  293,  307,
        311,  313,  317,  331,  337,  347,  349,  353,  359,  367,  373,  379,  383,  389,  397,  401,
        409,  419,  421,  431,  433,  439,  443,  449,  457,  461,  463,  467,  479,  487,  491,  499,
        503,  509,  521,  523,  541,  547,  557,  563,  569,  571,  577,  587,  593,  599,  601,  607,
        613,  617,  619,  631,  641,  643,  647,  653,  659,  661,  673,  677,  683,  691,  701,  709,
        719,  727,  733,  739,  743,  751,  757,  761,  769,  773,  787,  797,  809,  811,  821,  823,
        827,  829,  839,  853,  857,  859,  863,  877,  881,  883,  887,  907,  911,  919,  929,  937,
        941,  947,  953,  967,  971,  977,  983,  991,  997, 1009, 1013, 1019, 1021, 1031, 1033, 1039,
        1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153,
        1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279,
        1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
        1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499,
        1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613,
        1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741,
        1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873,
        1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999,
        2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113,
        2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251,
        2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371,
        2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477,
        2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647,
        2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731,
        2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857,
        2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001,
        3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163,
        3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299,
        3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407,
        3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539,
        3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659,
        3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793,
        3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919,
        3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051,
        4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201,
        4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327,
        4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463,
        4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603,
        4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733,
        4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903,
        4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009,
        5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153,
        5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303,
        5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441,
        5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569,
        5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701,
        5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843,
        5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987,
        6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131,
        6133, 6143}

    -- BIG INTEGER FUNCTIONS
    local function cmp(m, n)									-- Compare
        if #m == #n then
            local i = 1
            while m[i] and m[i] == n[i] do
                i += 1
            end
            return m[i] and m[i] > n[i]
        else
            return #m > #n
        end
    end
    local function add(m, n, t)									-- Addition
        table.clear(t)
        if #m == 1 and m[1] == 0 then
            return table.move(n, 1, #n, 1, t)
        elseif #n == 1 and n[1] == 0 then
            return table.move(m, 1, #m, 1, t)
        end
        m, n = if #m > #n then m else n, if #m > #n then n else m
        local c, d = 0, nil

        local i, j = #m, #n
        for _ = i, 1, - 1 do
            d = m[i] + (n[j] or 0) + c
            t[i], c = d % 16777216, if d > 16777215 then 1 else 0
            i -= 1
            j -= 1
        end
        if c == 1 then
            table.insert(t, 1, c)
        end

        return t
    end
    local function sub(m, n, t)									-- Substraction
        table.clear(t)
        local s = cmp(m, n)
        if s == nil then
            t[1] = 0
            return t, true
        end
        m, n = if s then m else n, if s then n else m
        if #m == 1 and m[1] == 0 then
            return table.move(n, 1, #n, 1, t), s
        elseif #n == 1 and n[1] == 0 then
            return table.move(m, 1, #m, 1, t), s
        end
        local c, d = 0, nil

        local i, j = #m, #n
        for _ = i, 1, - 1 do
            d = m[i] - (n[j] or 0) - c
            t[i], c = d % 16777216, if d < 0 then 1 else 0
            i -= 1
            j -= 1
        end
        while t[2] and t[1] == 0 do
            table.remove(t, 1)
        end

        return t, s
    end
    local function mul(m, n, t)									-- Multiplication
        table.clear(t)
        if (#m == 1 and m[1] == 0) or (#n == 1 and n[1] == 0) then
            t[1] = 0
            return t
        end
        m, n = if #m > #n then m else n, if #m > #n then n else m
        local d, c

        for i = #m, 1, - 1 do
            c = 0
            for j = #n, 1, - 1 do
                d = (t[i + j] or 0) + (n[j] or 0) * m[i] + c
                t[i + j], c = d % 16777216, math.floor(d / 16777216)
            end
            t[i] = c
        end
        while t[2] and t[1] == 0 do
            table.remove(t, 1)
        end

        return t
    end
    local function div(m, n, t1, t2, p1, p2)					-- Division and modulus
        table.clear	(t1)
        table.clear	(t2)
        t1[1] = 0
        table.move	(m, 1, #m, 1, t2)
        local s = true

        while cmp(t2, n) ~= false do
            table.clear(p1)
            if t2[1] < n[1] then
                p1[1] = math.floor((16777216 * t2[1] + t2[2]) / n[1])
                for i = 2, #t2 - #n do
                    p1[i] = 0
                end
            else
                p1[1] = math.floor(t2[1] / n[1])
                for i = 2, #t2 - #n + 1 do
                    p1[i] = 0
                end
            end

            table.clear(p2)
            table.move(t1, 1, #t1, 1, p2)
            _ = if s then add(p1, p2, t1) else sub(p1, p2, t1)
            table.clear(p2)
            mul(table.move(p1, 1, #p1, 1, p2), n, p1)
            table.clear(p2)
            table.move(t2, 1, #t2, 1, p2)
            _, s = sub(if s then p2 else p1, if s then p1 else p2, t2)
        end
        if not s then
            table.clear(p1)
            table.clear(p2)
            p2[1] = 1
            sub(table.move(t1, 1, #t1, 1, p1), p2, t1)
            table.clear(p1)
            sub(n, table.move(t2, 1, #t2, 1, p1), t2)
        end

        return t1, t2
    end
    local function lcm(m, n, t, p1, p2, p3, p4, p5)				-- Least common multiple
        table.clear(t)
        table.clear(p1)

        table.move(m, 1, #m, 1, t)
        table.move(n, 1, #n, 1, p1)
        while #p1 ~= 1 or p1[1] ~= 0 do 
            div(t, p1, p2, p3, p4, p5)
            table.clear(p2)
            table.move(t, 1, #t, 1, p2)

            table.clear(t)
            table.move(p1, 1, #p1, 1, t)
            table.clear(p1)
            table.move(p3, 1, #p3, 1, p1)
            table.clear(p3)
            table.move(p2, 1, #p2, 1, p3)
        end

        table.clear(p2)
        return div(mul(m, n, p1), table.move(t, 1, #t, 1, p2), t, p3, p4, p5)
    end --local e = 0
    local function pow(m, n, d, t, p1, p2, p3, p4, p5, p6)		-- Modular exponentiation
        table.clear	(t)
        table.clear	(p1)
        t[1] = 1
        table.move	(m, 1, #m, 1, p1)
        local c, i = n[#n] + 16777216, #n

        for _ = 1, math.log(n[1], 2) + (#n - 1) * 24 + 1 do --e+=1 if e % 800 == 0 then task.wait() end
            if c % 2 == 1 then
                div(mul(p1, t, p2), d, p3, t, p4, p5)
            end
            c = bit32.rshift(c, 1)
            if c == 1 then
                i -= 1
                c = (n[i] or 0) + 16777216
            end

            table.clear(p2)
            div(mul(table.move(p1, 1, #p1, 1, p2), p2, p3), d, p4, p1, p5, p6)
        end

        return t
    end
    local function inv(m, n, t, p1, p2, p3, p4, p5, p6, p7, p8) -- Modular multiplicative inverse
        table.clear	(t)
        table.clear	(p1)
        table.clear	(p2)
        table.clear	(p3)
        t[1] 	= 1
        p1[1] 	= 0
        table.move	(m, 1, #m, 1, p2)
        table.move	(n, 1, #n, 1, p3)
        local s1, s2, s3 = true, true, true

        while #p2 ~= 1 or p2[1] ~= 1 do
            div(p2, p3, p4, p5, p6, p7)
            table.clear	(p5)
            table.move	(p3, 1, #p3, 1, p5)
            div(p2, p5, p6, p3, p7, p8)
            table.clear	(p2)
            table.move	(p5, 1, #p5, 1, p2)
            table.clear	(p5)
            table.move	(p1, 1, #p1, 1, p5)

            s3 = s2
            mul(p1, p4, p6)
            if s1 == s2 then
                _, s2 = sub(t, p6, p1)
                s2 = if s1 then s2 else not s2
            else
                add(t, p6, p1)
                s2 = s1
            end
            table.move	(p5, 1, #p5, 1, t)
            s1 = s3
        end
        if not s1 then 
            table.clear(p1)
            sub(n, table.move(t, 1, #t, 1, p1), t)
        end

        return t
    end

    -- PROBABLY PRIME CHECKERS
    local function isDivisible	(a, p1, p2, p3, p4, p5) -- Checks if it is divisible by the first primes
        table.clear(p1)
        if #a == 1 and table.find(primes, a[1]) then
            return false
        end
        for _, p in pairs(primes) do
            p1[1] = p
            div(a, p1, p3, p2, p4, p5)
            if #p2 == 1 and p2[1] == 0 then
                return true
            end
        end
    end
    local function isPrime		(a, cnt, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, r) -- General test
        table.clear(p1)
        table.clear(p3)
        if #a == 0 then
            return false
        elseif #a == 1 and table.find(primes, a[1]) then
            return true
        end
        p1[1] = 1
        local k, c, i = 0, nil, nil

        sub(a, p1, p2)
        for _ = 1, cnt do -- Fermat's little theorem
            p1[1] = r:NextInteger	(0, p2[1] - 1)
            for j = 2, #p2 do
                p1[j] = r:NextInteger(0, 16777215)
            end
            p1[#p2] = math.max(p1[#p2], 2)
            while p1[1] == 0 do
                table.remove(p1, 1)
            end

            pow(p1, p2, a, p4, p5, p6, p7, p8, p9, p10)
            if #p4 ~= 1 or p4[1] ~= 1 then
                return false
            end
        end

        table.move(p2, 1, #p2, 1, p3)
        i = #p2
        while p2[i] == 0 do
            k += 24
            p3[i] = nil
            i -= 1
        end
        while p3[i] % 2 == 0 do
            k += 1
            c  = 0
            for j = 1, #p3 do
                p3[j], c = bit32.rshift(p3[j], 1) + bit32.lshift(c, 23), p3[j] % 2
            end
            if p3[1] == 0 then
                table.remove(p3, 1)
                i -= 1
            end
        end
        for _ = 1, cnt do -- Miller-Rabin primality test
            p1[1] = r:NextInteger	(0, p2[1] - 1)
            for j = 2, #p2 do
                p1[j] = r:NextInteger(0, 16777215)
            end
            p1[#p2] = math.max(p1[#p2], 2)
            while p1[1] == 0 do
                table.remove(p1, 1)
            end

            pow(p1, p3, a, p4, p5, p6, p7, p8, p9, p10)
            if #p4 == 1 and p4[1] == 1 or cmp(p2, p4) == nil then
                continue
            end
            i = true
            for _ = 1, k - 1 do
                table.clear	(p1)
                p1[1] = 2
                table.clear	(p5)
                table.move	(p4, 1, #p4, 1, p5)
                div(mul(p4, p5, p1), a, p5, p4, p6, p7)
                if #p4 == 1 and p4[1] == 1 then
                    return false
                elseif cmp(p2, p4) == nil then
                    i = false
                    break
                end
            end
            if i then
                return false
            end
        end
        return true
    end

    -- INITIALIZATION FUNCTIONS
    local function convertType(a, p1, p2, p3, p4) -- Converts data to bigInt if possible
        local t, n = {}, nil
        if type(a) == "number" then
            assert(a == a and a >= 0 and math.abs(a) ~= math.huge, "Unable to cast value to bigInt")
            a = math.floor(a)
            while a ~= 0 do
                table.insert(t, 1, a % 16777216)
                a = math.floor(a / 16777216)
            end
        elseif type(a) == "string" then
            if string.match(a, "^[0_]*$") then
                t[1] = 0
            elseif string.match(a, "^_*0_*[Xx][%x_]+$") or string.match(a, "^_*0_*[Bb][01_]+$") then
                local x = if string.match(a, "[Xx]") then 16 else 2
                n = string.gsub(string.match(a, "0_*.[0_]*(.+)"), "_", "")
                n = string.rep("0", - string.len(n) % if x == 16 then 6 else 24) .. n
                for i in string.gmatch(n, "(......" .. if x == 16 then ")" else "..................)")
                do
                    table.insert(t, tonumber(i, x))
                end
            elseif string.match(a, "^_*[%d_]*%.?[%d_]*$") then
                table.clear(p1)
                table.clear(p2)
                p1[1] = 10000000
                p2[1] = 1
                n = string.gsub(string.match(a, "_*[0_]*([%d_]*)%.?.-$"), "_", "")
                n = string.rep("0", - string.len(n) % 7) .. n
                for i in string.gmatch(string.reverse(n), "(.......)") do
                    table.clear(p3)
                    p3[1] = tonumber(string.reverse(i))
                    mul(p3, p2, p4)
                    table.clear(p3)
                    add(p4, table.move(t, 1, #t, 1, p3), t)
                    table.clear(p3)
                    mul(table.move(p2, 1, #p2, 1, p3), p1, p2)
                end
            else
                error("Unable to cast value to bigInt")
            end
        elseif type(a) == "table" then
            for i, j in ipairs(a) do
                assert(type(j) == "number" and math.floor(j) == j and 0 <= j and j < 16777216,
                    "Unable to cast value to bigInt")
                t[i] = j
            end
            if #t == 0 then
                t[1] = 0
            end
        else
            error("Unable to cast value to bigInt")
        end
        return t
    end
    type bigInt = {number} -- Type instance of a valid bigInt object
    type bytes 	= {number} -- Type instance of a valid bytes object

    -- MAIN ALGORITHM
   return {
        -- Keys generation constructor
        newKeys 	= function(p : number | bigInt, q : bigInt?, e : bigInt?) 			: (bigInt, bigInt,
            bigInt, bigInt, bigInt, bigInt)
            local p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14 = {}, {}, {}, {}, {}, {}, {}
            , {}, {}, {}, {}, {}, {}, {}
            if q == nil then
                local l = math.floor(tonumber(p) or 256)
                assert(2 < l and l < 4294967296, "Invalid key length")
                local r1, r2, mm = Random.new(), Random.new(), bit32.lshift(1, (l - 1) % 24)
                local ml = bit32.lshift(mm, 1) - 1
                p, q, l = {}, {}, math.ceil(l / 24)

                while not isPrime(p, 5, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, r1) do
                    p[1] = r1:NextInteger(mm, ml)
                    for i = 2, l do
                        p[i] = r1:NextInteger(0, 16777215)
                    end
                    if p[l] % 2 == 0 then
                        p[l] += 1
                    end

                    table.clear(p1)
                    p1[1] = 2
                    while isDivisible(p, p2, p3, p4, p5, p6) do
                        add(table.move(p, 1, #p, 1, p2), p1, p)
                    end
                end
                while cmp(p, q) == nil or not isPrime(q, 5, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, r2) do
                    q[1] = r2:NextInteger(mm, ml)
                    for i = 2, l do
                        q[i] = r2:NextInteger(0, 16777215)
                    end
                    if q[l] % 2 == 0 then
                        q[l] += 1
                    end

                    table.clear(p1)
                    p1[1] = 2
                    while isDivisible(q, p2, p3, p4, p5, p6) do
                        add(table.move(q, 1, #q, 1, p2), p1, q)
                    end
                end
            else
                p, q = convertType(p, p1, p2, p3, p4), convertType(q, p1, p2, p3, p4)
                e = if e == nil then nil else convertType(e, p1, p2, p3, p4)
            end
            table.clear(p1)

            p1[1] = 1
            lcm(sub(p, p1, p2), sub(q, p1, p3), p4, p5, p6, p7, p8, p9)
            e = if not e then {if #p4 == 1 and p4[1] < 65538 then 3 else 65537} else e
            div(p4, e, p6, p5, p7, p8)
            assert(#p5 ~= 1 or p5[1] ~= 0, "Invalid values for 'p', 'q' and/or 'e'")
            inv(e, p4, p6, p7, p8, p9, p10, p11, p12, p13, p14)
            div(p6, p2, p8, p7, p9, p10)
            div(p6, p3, p9, p8, p10, p11)
            return mul(p, q, p5), e, p6, p, q, p7, p8, inv(q, p, p9, p10, p11, p12, p13, p14, {}, {}, {})
        end,
        -- Encryption, decryption and sign
        crypt 		= function(n : bigInt, text : bigInt, key : bigInt) 				: bigInt
            local p1, p2, p3, p4 = {}, {}, {}, {}
            n, text = convertType(n, p1, p2, p3, p4), convertType(text, p1, p2, p3, p4)
            assert(cmp(n, text), "Text must not exceed 'n'")
            key 	= convertType(key, p1, p2, p3, p4)

            return pow(text, key, n, p1, p2, p3, p4, {}, {}, {})
        end,
        decrypt_CRT = function(n : bigInt, cipherText : bigInt, p: bigInt, q : bigInt, d_p : bigInt, d_q :
            bigInt, q_inv : bigInt) : bigInt
                local p1, p2, p3, p4, p5, p6, p7, p8 = {}, {}, {}, {}, {}, {}, {}, {}
                n, cipherText 		= convertType(n, p1, p2, p3, p4), convertType(cipherText, p1, p2, p3, p4)
                p, q, d_q, q_inv 	= convertType(p, p1, p2, p3, p4), convertType(q, p1, p2, p3, p4),
                convertType(d_q, p1, p2, p3, p4), convertType(q_inv, p1, p2, p3, p4)

                pow(cipherText, d_p, p, p1, p2, p3, p4, p5, p6, p7)
                pow(cipherText, d_q, q, p2, p3, p4, p5, p6, p7, p8)
                sub(p1, p2, p3)
                if cmp(p1, p2) == false then
                div(q, p, p4, p5, p6, p7)
                if #p5 ~= 1 or p5[1] ~= 0 then
                    table.clear(p5)
                    table.clear(p6)
                    p6[1] = 1
                    add(table.move(p4, 1, #p4, 1, p5), p6, p4)
                end
                table.clear(p5)
                sub(mul(p4, p, p6), table.move(p3, 1, #p3, 1, p5), p3)
            end
                div(mul(p3, q_inv, p4), p, p5, p3, p6, p7)
                div(add(mul(p3, q, p1), p2, p3), n, p2, p4, p5, p6)

                return p4
            end,
        -- Signature verification
        verify 		= function(hash_1 : bigInt, hash_2 : bigInt) 						: boolean
            local p1, p2, p3, p4 = {}, {}, {}, {}
            hash_1, hash_2 = convertType(hash_1, p1, p2, p3, p4), convertType(hash_2, p1, p2, p3, p4)

            return cmp(hash_1, hash_2) == nil
        end,

        -- Data type conversion of bigInt and bytes
        to_bigInt 	= function(a : bytes) 	: bigInt
            local r, n, x
            if type(a) == "number" then
                if math.abs(a) == math.huge then
                    r = table.create(6, 0)
                    table.insert		(r, 1, 240)
                    table.insert		(r, 1, if a < 0 then 255 else 127)
                elseif a == 0 then
                    r = table.create(7, 0)
                    table.insert		(r, 1, if 1 / a < 0 then 128 else 0)	
                elseif a ~= a then
                    r = {127, 240, 0, 0, 0, 0, 0, 1}
                elseif math.abs(a) < 2.2250738585072014e-308 then
                    r, a = {if a < 0 then 128 else 0}, math.abs(a) 
                    local a, e = math.frexp(a)
                    a 	 *= 2 ^ - (e + 970)
                    for i = 1, 7 do
                        table.insert	(r, 2, a % 256)
                        a = math.floor	(a / 256)
                    end
                else
                    r, a = {if a < 0 then 128 else 0}, math.abs(a)
                    local e = math.round(math.log(a, 2))
                    r[2]  = (e + 1023) % 16 * 16
                    r[1] += math.floor((e + 1023) / 16)
                    a = (a * 2 ^ - e % 1) * 4503599627370496
                    for i = 1, 6 do
                        table.insert	(r, 3, a % 256)
                        a = math.floor	(a / 256)
                    end
                    r[2] += a
                end
            elseif type(a) == "string" then
                assert(a ~= "", "Unable to cast value to bytes")
                r = {}
                for i = 1, string.len(a), 7997 do
                    table.move({string.byte(a, i, i + 7996)}, 1, 7997, i, r)
                end
            elseif type(a) == "table" then
                assert(#a ~= 0, "Unable to cast value to bytes")
                r = {}
                for _, i in ipairs(a) do
                    assert(type(i) == "number" and math.floor(i) == i and 0 <= i and i < 256,
                        "Unable to cast value to bytes")
                    r[i] = i
                end
            end

            for _ = 1, - #r % 3 do
                table.insert(r, 1, 0)
            end
            for _ = 1, #r / 3 do
                n = bit32.lshift(r[1], 16) + bit32.lshift(r[2], 8) + r[3]
                if x or n ~= 0 then
                    table.insert(r, n)
                    x = true
                end
                table.remove(r, 1)
                table.remove(r, 1)
                table.remove(r, 1)
            end
            return r
        end,
        to_bytes 	= function(a : bigInt) 	: bytes
            a = convertType(a)

            for _ = 1, #a do
                table.insert(a, bit32.rshift(a[1], 16))
                table.insert(a, bit32.rshift(a[1], 8) % 256)
                table.insert(a, a[1] % 256)
                table.remove(a, 1)
            end
            return a
        end
    } -- Returns the library
    
end

return RoCrypt
