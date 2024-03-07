--[[
RoCrypt
----------------------------------------------------------------------------------------
DESCRIPTION:
	This module contains cryptographic hash functions (CHF)
	   MD5 
	   SHA-224, SHA-256, SHA-384, SHA-512
	Cyclic redundancy checks (CRC) algorithms
        CRC32
    Binary-to-hex/encoding algorithms
        BASE64
    Asymmetric algorithms
        RSA
    UID (unique identifier) algorithms
        Snowflake
	All written in pure Lua.
USAGE:
	Input data should be a string
	Result (SHA digest) is returned in hexadecimal representation as a string of lowercase hex digits.
	Simplest usage example:
		local RoCrypt = require(script.RoCrypt)
		local hash = RoCrypt.sha256("string here")
	Cryptographic functions:
		RoCrypt.sha256
		RoCrypt.sha224
		RoCrypt.sha384
		RoCrypt.sha512
		RoCrypt.crc32
		RoCrypt.rsa
		RoCrypt.base64
		              .decode()
		              .encode()
		RoCrypt.md5
----------------------------------------------------------------------------------------
CREDIT: RobloxGamerPro200007 - RSA function
--]]--

RoCrypt = {}
band, bxor, bnot, rrotate, rshift, bor, lrotate, lshift = bit32.band, bit32.bxor, bit32.bnot, bit32.rrotate, bit32.rshift, bit32.bor, bit32.lrotate, bit32.lshift
char, rep, sub, format, byte = string.char, string.rep, string.sub, string.format, string.byte
floor = math.floor
bit = bit32
persistent = {
    snowflake = {
        id = nil,
        increment = 0
    },
    md5 = {
        common_W = {}
    },
    sha_backbone = function()
        local AND_of_two_bytes = {}  -- look-up table (256*256 entries)
        for idx = 0, 65535 do
            local x = idx % 256
            local y = (idx - x) / 256
            local res = 0
            local w = 1
            while x * y ~= 0 do
                local rx = x % 2
                local ry = y % 2
                res = res + rx * ry * w
                x = (x - rx) / 2
                y = (y - ry) / 2
                w = w * 2
            end
            AND_of_two_bytes[idx] = res
        end





        local function HEX(x)
            return string.format("%08x", x % 4294967296)
        end
        local sha2_K_lo, sha2_K_hi, sha2_H_lo, sha2_H_hi = {}, {}, {}, {}
        local sha2_H_ext256 = {[224] = {}, [256] = sha2_H_hi}
        local sha2_H_ext512_lo, sha2_H_ext512_hi = {[384] = {}, [512] = sha2_H_lo}, {[384] = {}, [512] = sha2_H_hi}

        local common_W = {}

        local function sha256_feed_64(H, K, str, W, offs, size)
            for pos = offs, size + offs - 1, 64 do
                for j = 1, 16 do
                    pos = pos + 4
                    local a, b, c, d = byte(str, pos - 3, pos)
                    W[j] = ((a * 256 + b) * 256 + c) * 256 + d
                end
                for j = 17, 64 do
                    local a, b = W[j-15], W[j-2]
                    W[j] = bxor(rrotate(a, 7), lrotate(a, 14), rshift(a, 3)) + bxor(lrotate(b, 15), lrotate(b, 13), rshift(b, 10)) + W[j-7] + W[j-16]
                end
                local a, b, c, d, e, f, g, h, z = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8], nil
                for j = 1, 64 do
                    z = bxor(rrotate(e, 6), rrotate(e, 11), lrotate(e, 7)) + band(e, f) + band(-1-e, g) + h + K[j] + W[j]
                    h = g
                    g = f
                    f = e
                    e = z + d
                    d = c
                    c = b
                    b = a
                    a = z + band(d, c) + band(a, bxor(d, c)) + bxor(rrotate(a, 2), rrotate(a, 13), lrotate(a, 10))
                end
                H[1], H[2], H[3], H[4] = (a + H[1]) % 4294967296, (b + H[2]) % 4294967296, (c + H[3]) % 4294967296, (d + H[4]) % 4294967296
                H[5], H[6], H[7], H[8] = (e + H[5]) % 4294967296, (f + H[6]) % 4294967296, (g + H[7]) % 4294967296, (h + H[8]) % 4294967296
            end
        end

        local function sha512_feed_128(H_lo, H_hi, K_lo, K_hi, str, W, offs, size)
            -- offs >= 0, size >= 0, size is multiple of 128
            -- W1_hi, W1_lo, W2_hi, W2_lo, ...   Wk_hi = W[2*k-1], Wk_lo = W[2*k]
            for pos = offs, size + offs - 1, 128 do
                for j = 1, 32 do
                    pos = pos + 4
                    local a, b, c, d = byte(str, pos - 3, pos)
                    W[j] = ((a * 256 + b) * 256 + c) * 256 + d
                end
                local tmp1, tmp2
                for jj = 17 * 2, 80 * 2, 2 do
                    local a_lo, a_hi, b_lo, b_hi = W[jj-30], W[jj-31], W[jj-4], W[jj-5]
                    tmp1 = bxor(rshift(a_lo, 1) + lshift(a_hi, 31), rshift(a_lo, 8) + lshift(a_hi, 24), rshift(a_lo, 7) + lshift(a_hi, 25)) + bxor(rshift(b_lo, 19) + lshift(b_hi, 13), lshift(b_lo, 3) + rshift(b_hi, 29), rshift(b_lo, 6) + lshift(b_hi, 26)) + W[jj-14] + W[jj-32]
                    tmp2 = tmp1 % 4294967296
                    W[jj-1] = bxor(rshift(a_hi, 1) + lshift(a_lo, 31), rshift(a_hi, 8) + lshift(a_lo, 24), rshift(a_hi, 7)) + bxor(rshift(b_hi, 19) + lshift(b_lo, 13), lshift(b_hi, 3) + rshift(b_lo, 29), rshift(b_hi, 6)) + W[jj-15] + W[jj-33] + (tmp1 - tmp2) / 4294967296
                    W[jj] = tmp2
                end
                local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo, z_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8], nil
                local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi, z_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8], nil
                for j = 1, 80 do
                    local jj = 2 * j
                    tmp1 = bxor(rshift(e_lo, 14) + lshift(e_hi, 18), rshift(e_lo, 18) + lshift(e_hi, 14), lshift(e_lo, 23) + rshift(e_hi, 9)) + band(e_lo, f_lo) + band(-1-e_lo, g_lo) + h_lo + K_lo[j] + W[jj]
                    z_lo = tmp1 % 4294967296
                    z_hi = bxor(rshift(e_hi, 14) + lshift(e_lo, 18), rshift(e_hi, 18) + lshift(e_lo, 14), lshift(e_hi, 23) + rshift(e_lo, 9)) + band(e_hi, f_hi) + band(-1-e_hi, g_hi) + h_hi + K_hi[j] + W[jj-1] + (tmp1 - z_lo) / 4294967296
                    h_lo = g_lo
                    h_hi = g_hi
                    g_lo = f_lo
                    g_hi = f_hi
                    f_lo = e_lo
                    f_hi = e_hi
                    tmp1 = z_lo + d_lo
                    e_lo = tmp1 % 4294967296
                    e_hi = z_hi + d_hi + (tmp1 - e_lo) / 4294967296
                    d_lo = c_lo
                    d_hi = c_hi
                    c_lo = b_lo
                    c_hi = b_hi
                    b_lo = a_lo
                    b_hi = a_hi
                    tmp1 = z_lo + band(d_lo, c_lo) + band(b_lo, bxor(d_lo, c_lo)) + bxor(rshift(b_lo, 28) + lshift(b_hi, 4), lshift(b_lo, 30) + rshift(b_hi, 2), lshift(b_lo, 25) + rshift(b_hi, 7))
                    a_lo = tmp1 % 4294967296
                    a_hi = z_hi + (band(d_hi, c_hi) + band(b_hi, bxor(d_hi, c_hi))) + bxor(rshift(b_hi, 28) + lshift(b_lo, 4), lshift(b_hi, 30) + rshift(b_lo, 2), lshift(b_hi, 25) + rshift(b_lo, 7)) + (tmp1 - a_lo) / 4294967296
                end
                tmp1 = H_lo[1] + a_lo
                tmp2 = tmp1 % 4294967296
                H_lo[1], H_hi[1] = tmp2, (H_hi[1] + a_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
                tmp1 = H_lo[2] + b_lo
                tmp2 = tmp1 % 4294967296
                H_lo[2], H_hi[2] = tmp2, (H_hi[2] + b_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
                tmp1 = H_lo[3] + c_lo
                tmp2 = tmp1 % 4294967296
                H_lo[3], H_hi[3] = tmp2, (H_hi[3] + c_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
                tmp1 = H_lo[4] + d_lo
                tmp2 = tmp1 % 4294967296
                H_lo[4], H_hi[4] = tmp2, (H_hi[4] + d_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
                tmp1 = H_lo[5] + e_lo
                tmp2 = tmp1 % 4294967296
                H_lo[5], H_hi[5] = tmp2, (H_hi[5] + e_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
                tmp1 = H_lo[6] + f_lo
                tmp2 = tmp1 % 4294967296
                H_lo[6], H_hi[6] = tmp2, (H_hi[6] + f_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
                tmp1 = H_lo[7] + g_lo
                tmp2 = tmp1 % 4294967296
                H_lo[7], H_hi[7] = tmp2, (H_hi[7] + g_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
                tmp1 = H_lo[8] + h_lo
                tmp2 = tmp1 % 4294967296
                H_lo[8], H_hi[8] = tmp2, (H_hi[8] + h_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
            end
        end

        --------------------------------------------------------------------------------
        -- CALCULATING THE MAGIC NUMBERS (roots of primes)
        --------------------------------------------------------------------------------

        do
            local function mul(src1, src2, factor, result_length)
                -- Long arithmetic multiplication: src1 * src2 * factor
                -- src1, src2 - long integers (arrays of digits in base 2^24)
                -- factor - short integer
                local result = {}
                local carry = 0
                local value = 0.0
                local weight = 1.0
                for j = 1, result_length do
                    local prod = 0
                    for k = math.max(1, j + 1 - #src2), math.min(j, #src1) do
                        prod = prod + src1[k] * src2[j + 1 - k]
                    end
                    carry = carry + prod * factor
                    local digit = carry % 16777216
                    result[j] = digit
                    carry = floor(carry / 16777216)
                    value = value + digit * weight
                    weight = weight * 2^24
                end
                return result,value
            end

            local idx, step, p, one  = 0, {4, 1, 2, -2, 2}, 4, {1}
            local sqrt_hi, sqrt_lo, idx_disp = sha2_H_hi, sha2_H_lo, 0
            repeat
                p = p + step[p % 6]
                local d = 1
                repeat
                    d = d + step[d % 6]
                    if d * d > p then
                        idx = idx + 1
                        local root = p^(1/3)
                        local R = mul({floor(root * 2^40)}, one, 1, 2)
                        local _, delta = mul(R, mul(R, R, 1, 4), -1, 4)
                        local hi = R[2] % 65536 * 65536 + floor(R[1] / 256)
                        local lo = R[1] % 256 * 16777216 + floor(delta * (2^-56 / 3) * root / p)
                        sha2_K_hi[idx], sha2_K_lo[idx] = hi, lo
                        if idx < 17 then
                            root = p^(1/2)
                            R = mul({floor(root * 2^40)}, one, 1, 2)
                            _, delta = mul(R, R, -1, 2)
                            hi = R[2] % 65536 * 65536 + floor(R[1] / 256)
                            lo = R[1] % 256 * 16777216 + floor(delta * 2^-17 / root)
                            sha2_H_ext256[224][idx + idx_disp] = lo
                            sqrt_hi[idx + idx_disp], sqrt_lo[idx + idx_disp] = hi, lo
                            if idx == 8 then
                                sqrt_hi, sqrt_lo, idx_disp = sha2_H_ext512_hi[384], sha2_H_ext512_lo[384], -8
                            end
                        end
                        break
                    end
                until p % d == 0
            until idx > 79
        end

        -- Calculating IV for SHA512/224 and SHA512/256
        for width = 224, 256, 32 do
            local H_lo, H_hi = {}, {}
            for j = 1, 8 do
                H_lo[j] = bxor(sha2_H_lo[j], 0xa5a5a5a5)
                H_hi[j] = bxor(sha2_H_hi[j], 0xa5a5a5a5)
            end
            sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, "SHA-512/"..tonumber(width).."\128"..string.rep("\0", 115).."\88", common_W, 0, 128)
            sha2_H_ext512_lo[width] = H_lo
            sha2_H_ext512_hi[width] = H_hi
        end


        --------------------------------------------------------------------------------
        -- FINAL FUNCTIONS
        --------------------------------------------------------------------------------

        function sha256ext(width, text)

            -- Create an instance (private objects for current calculation)
            local H, length, tail = {unpack(sha2_H_ext256[width])}, 0, ""

            local function partial(text_part)
                if text_part then
                    if tail then
                        length = length + #text_part
                        local offs = 0
                        if tail ~= "" and #tail + #text_part >= 64 then
                            offs = 64 - #tail
                            sha256_feed_64(H, sha2_K_hi, tail..sub(text_part, 1, offs), common_W, 0, 64)
                            tail = ""
                        end
                        local size = #text_part - offs
                        local size_tail = size % 64
                        sha256_feed_64(H, sha2_K_hi, text_part, common_W, offs, size - size_tail)
                        tail = tail..sub(text_part, #text_part + 1 - size_tail)
                        return partial
                    else
                        error("Adding more chunks is not allowed after asking for final result", 2)
                    end
                else
                    if tail then
                        local final_blocks = {tail, "\128", string.rep("\0", (-9 - length) % 64 + 1)}
                        tail = nil
                        -- Assuming user data length is shorter than 2^53 bytes
                        -- Anyway, it looks very unrealistic that one would spend enough time to process a 2^53 bytes of data by using this Lua script :-)
                        -- 2^53 bytes = 2^56 bits, so "bit-counter" fits in 7 bytes
                        length = length * (8 / 256^7)  -- convert "byte-counter" to "bit-counter" and move floating point to the left
                        for j = 4, 10 do
                            length = length % 1 * 256
                            final_blocks[j] = char(floor(length))
                        end
                        final_blocks = table.concat(final_blocks)
                        sha256_feed_64(H, sha2_K_hi, final_blocks, common_W, 0, #final_blocks)
                        local max_reg = width / 32
                        for j = 1, max_reg do
                            H[j] = HEX(H[j])
                        end
                        H = table.concat(H, "", 1, max_reg)
                    end
                    return H
                end
            end

            if text then
                -- Actually perform calculations and return the SHA256 digest of a message
                return partial(text)()
            else
                -- Return function for partial chunk loading
                -- User should feed every chunks of input data as single argument to this function and receive SHA256 digest by invoking this function without an argument
                return partial
            end

        end


        function sha512ext(width, text)

            -- Create an instance (private objects for current calculation)
            local length, tail, H_lo, H_hi = 0, "", {unpack(sha2_H_ext512_lo[width])}, {unpack(sha2_H_ext512_hi[width])}

            local function partial(text_part)
                if text_part then
                    if tail then
                        length = length + #text_part
                        local offs = 0
                        if tail ~= "" and #tail + #text_part >= 128 then
                            offs = 128 - #tail
                            sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, tail..sub(text_part, 1, offs), common_W, 0, 128)
                            tail = ""
                        end
                        local size = #text_part - offs
                        local size_tail = size % 128
                        sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, text_part, common_W, offs, size - size_tail)
                        tail = tail..sub(text_part, #text_part + 1 - size_tail)
                        return partial
                    else
                        error("Adding more chunks is not allowed after asking for final result", 2)
                    end
                else
                    if tail then
                        local final_blocks = {tail, "\128", string.rep("\0", (-17-length) % 128 + 9)}
                        tail = nil
                        -- Assuming user data length is shorter than 2^53 bytes
                        -- 2^53 bytes = 2^56 bits, so "bit-counter" fits in 7 bytes
                        length = length * (8 / 256^7)  -- convert "byte-counter" to "bit-counter" and move floating point to the left
                        for j = 4, 10 do
                            length = length % 1 * 256
                            final_blocks[j] = char(floor(length))
                        end
                        final_blocks = table.concat(final_blocks)
                        sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, final_blocks, common_W, 0, #final_blocks)
                        local max_reg = math.ceil(width / 64)
                        for j = 1, max_reg do
                            H_lo[j] = HEX(H_hi[j])..HEX(H_lo[j])
                        end
                        H_hi = nil
                        H_lo = table.concat(H_lo, "", 1, max_reg):sub(1, width / 4)
                    end
                    return H_lo
                end
            end

            if text then
                -- Actually perform calculations and return the SHA256 digest of a message
                return partial(text)()
            else
                -- Return function for partial chunk loading
                -- User should feed every chunks of input data as single argument to this function and receive SHA256 digest by invoking this function without an argument
                return partial
            end

        end


    end
}

persistent["sha_backbone"]()


function RoCrypt.sha224(message: string)
    return sha256ext(224, message)
end

function RoCrypt.sha256(message: string)
    return sha256ext(256, message)
end

function RoCrypt.sha384(message: string)
    return sha512ext(384, message)
end

function RoCrypt.sha512(message: string)
    return sha512ext(512, message)
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

function RoCrypt.base64()
    local base64chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

    local function encode(data)
        return (data:gsub(".", function(x)
            local r, b = "", byte(x)
            for i = 8, 1, -1 do
                r = r .. (b % 2 ^ i - b % 2 ^ (i - 1) > 0 and "1" or "0")
            end
            return r
        end) .. "0000"):gsub("%d%d%d?%d?%d?%d?", function(x)
            if #x < 6 then
                return ""
            end
            local c = 0
            for i = 1, 6 do
                c = c + (sub(x, i, i) == "1" and 2 ^ (6 - i) or 0)
            end
            return sub(base64chars, c + 1, c + 1)
        end) .. ({ "", "==", "=" })[#data % 3 + 1]
    end

    local function decode(data)
        data = string.gsub(data, "[^" .. base64chars .. "=]", "")
        return (data:gsub(".", function(x)
            if x == "=" then
                return ""
            end
            local r, f = "", (string.find(base64chars, x) - 1)
            for i = 6, 1, -1 do
                r = r .. (f % 2 ^ i - f % 2 ^ (i - 1) > 0 and "1" or "0")
            end
            return r
        end):gsub("%d%d%d?%d?%d?%d?%d?%d?", function(x)
            if #x ~= 8 then
                return ""
            end
            local c = 0
            for i = 1, 8 do
                c = c + (sub(x, i, i) == "1" and 2 ^ (8 - i) or 0)
            end
            return char(c)
        end))
    end

    return {
        encode = encode,
        decode = decode
    }
end

function RoCrypt.md5(message: string)
    local md5_K, md5_sha1_H = {}, {0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0}
    local md5_next_shift = {0, 0, 0, 0, 0, 0, 0, 0, 28, 25, 26, 27, 0, 0, 10, 9, 11, 12, 0, 15, 16, 17, 18, 0, 20, 22, 23, 21}


    local function md5_feed_64(H, str, offs, size)
        -- offs >= 0, size >= 0, size is multiple of 64
        local W, K, md5_next_shift = persistent["md5"]["common_W"], md5_K, md5_next_shift
        local h1, h2, h3, h4 = H[1], H[2], H[3], H[4]
        for pos = offs, offs + size - 1, 64 do
            for j = 1, 16 do
                pos = pos + 4
                local a, b, c, d = string.byte(str, pos - 3, pos)
                W[j] = ((d * 256 + c) * 256 + b) * 256 + a
            end

            local a, b, c, d = h1, h2, h3, h4
            local s = 25
            for j = 1, 16 do
                local F = bit32.rrotate(bit32.band(b, c) + bit32.band(-1 - b, d) + a + K[j] + W[j], s) + b
                s = md5_next_shift[s]
                a = d
                d = c
                c = b
                b = F
            end

            s = 27
            for j = 17, 32 do
                local F = bit32.rrotate(bit32.band(d, b) + bit32.band(-1 - d, c) + a + K[j] + W[(5 * j - 4) % 16 + 1], s) + b
                s = md5_next_shift[s]
                a = d
                d = c
                c = b
                b = F
            end

            s = 28
            for j = 33, 48 do
                local F = bit32.rrotate(bit32.bxor(bit32.bxor(b, c), d) + a + K[j] + W[(3 * j + 2) % 16 + 1], s) + b
                s = md5_next_shift[s]
                a = d
                d = c
                c = b
                b = F
            end

            s = 26
            for j = 49, 64 do
                local F = bit32.rrotate(bit32.bxor(c, bit32.bor(b, -1 - d)) + a + K[j] + W[(j * 7 - 7) % 16 + 1], s) + b
                s = md5_next_shift[s]
                a = d
                d = c
                c = b
                b = F
            end

            h1 = (a + h1) % 4294967296
            h2 = (b + h2) % 4294967296
            h3 = (c + h3) % 4294967296
            h4 = (d + h4) % 4294967296
        end

        H[1], H[2], H[3], H[4] = h1, h2, h3, h4
    end
    -- Constants for MD5
    do
        for idx = 1, 64 do
            -- we can't use formula math.floor(abs(sin(idx))*TWO_POW_32) because its result may be beyond integer range on Lua built with 32-bit integers
            local hi, lo = math.modf(math.abs(math.sin(idx)) * 2^16)
            md5_K[idx] = hi * 65536 + math.floor(lo * 2^16)
        end
    end





    -- Create an instance (private objects for current calculation)
    local H, length, tail = table.create(4), 0, ""
    H[1], H[2], H[3], H[4] = md5_sha1_H[1], md5_sha1_H[2], md5_sha1_H[3], md5_sha1_H[4]

    local function partial(message_part)
        if message_part then
            local partLength = #message_part
            if tail then
                length = length + partLength
                local offs = 0
                if tail ~= "" and #tail + partLength >= 64 then
                    offs = 64 - #tail
                    md5_feed_64(H, tail .. string.sub(message_part, 1, offs), 0, 64)
                    tail = ""
                end

                local size = partLength - offs
                local size_tail = size % 64
                md5_feed_64(H, message_part, offs, size - size_tail)
                tail = tail .. string.sub(message_part, partLength + 1 - size_tail)
                return partial
            else
                error("Adding more chunks is not allowed after receiving the result", 2)
            end
        else
            if tail then
                local final_blocks = table.create(3) --{tail, "\128", string.rep("\0", (-9 - length) % 64)}
                final_blocks[1] = tail
                final_blocks[2] = "\128"
                final_blocks[3] = string.rep("\0", (-9 - length) % 64)
                tail = nil
                length = length * 8 -- convert "byte-counter" to "bit-counter"
                for j = 4, 11 do
                    local low_byte = length % 256
                    final_blocks[j] = string.char(low_byte)
                    length = (length - low_byte) / 256
                end

                final_blocks = table.concat(final_blocks)
                md5_feed_64(H, final_blocks, 0, #final_blocks)
                for j = 1, 4 do
                    H[j] = string.format("%08x", H[j] % 4294967296)
                end

                H = string.gsub(table.concat(H), "(..)(..)(..)(..)", "%4%3%2%1")
            end

            return H
        end
    end

    if message then
        -- Actually perform calculations and return the MD5 digest of a message
        return partial(message)()
    else
        -- Return function for chunk-by-chunk loading
        -- User should feed every chunk of input data as single argument to this function and finally get MD5 digest by invoking this function without an argument
        return partial
    end




end

    

return RoCrypt
