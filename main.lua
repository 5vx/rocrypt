--[[
RoCrypt
----------------------------------------------------------------------------------------
DESCRIPTION:
    TODO: BLAKE3, BLAKE2S, BLAKE2B
	This module contains cryptographic hash functions (CHF)
	   MD2, MD4, MD5 
	   RIPEMD-128, RIPEMD-160
	   SHA1, SHA-224, SHA-256, SHA-384, SHA-512
	Cyclic redundancy checks (CRC) algorithms
        CRC32
    Binary-to-hex/encoding algorithms
        BASE64
        BASE91
    Asymmetric algorithms
        RSA
    Symmetric algorithms
        AES
    Shared-secret algorithms
        HMAC
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
		RoCrypt.sha256()
		RoCrypt.sha224()
		RoCrypt.sha384()
		RoCrypt.sha512()
		RoCrypt.crc32()
		RoCrypt.rsa
		    .crypt()
		    .newKeys()
		    .verify()
		RoCrypt.base64
		    .encode()
		    .decode()
		RoCrypt.base91
		    .encode()
		    .decode()
		RoCrypt.md2()
		RoCrypt.md4()
		RoCrypt.md5()
		RoCrypt.aes
		    .encrypt_CTR()
		    .encrypt_CFB()
		    .decrypt_CFB()
		    .encrypt_ECB()
		    .decrypt_ECB()
		    .encrypt_CBC()
		    .decrypt_CBC()
		    .encrypt_OFB()
		    .encrypt_PCBC()
		    .decrypt_PCBC()
        RoCrypt.ripemd128()
        RoCrypt.ripemd160()
		           
----------------------------------------------------------------------------------------
CREDIT: RobloxGamerPro200007 - RSA, AES function
github.com/somesocks/lua-lockbox
--]]--



RoCrypt = {
    utils = {
    }
}

--[[--
    aliases (so as to save on memory)
]]--
local ipairs = ipairs
band, bxor, bnot, rrotate, rshift, bor, lrotate, lshift, extract = bit32.band, bit32.bxor, bit32.bnot, bit32.rrotate, bit32.rshift, bit32.bor, bit32.lrotate, bit32.lshift, bit32.extract
char, rep, sub, format, byte = string.char, string.rep, string.sub, string.format, string.byte
floor = math.floor
bit, E = bit32, nil
persistent = {
    snowflake = {
        id = nil,
        increment = 0
    },
    md5 = {
        common_W = {}
    },
    sha_backbone = (function()
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


    end)()
}



-- @github.com/somesocks/lua-lockbox
function RoCrypt.utils.queue()
    local Queue = function()
        local queue = {};
        local tail = 0;
        local head = 0;

        local public = {};

        public.push = function(obj)
            queue[head] = obj;
            head = head + 1;
            return;
        end

        public.pop = function()
            if tail < head
            then
                local obj = queue[tail];
                queue[tail] = nil;
                tail = tail + 1;
                return obj;
            else
                return nil;
            end
        end

        public.size = function()
            return head - tail;
        end

        public.getHead = function()
            return head;
        end

        public.getTail = function()
            return tail;
        end

        public.reset = function()
            queue = {};
            head = 0;
            tail = 0;
        end

        return public;
    end

    return Queue();

end
function RoCrypt.utils.bytes2word(b0,b1,b2,b3)
    local i = b3; i = lshift(i, 8)
    i = bor(i, b2); i = lshift(i, 8)
    i = bor(i, b1); i = lshift(i, 8)
    i = bor(i, b0)
    return i
end

function RoCrypt.utils.word2bytes(word)
    local b0, b1, b2, b3
    b0 = band(word, 0xFF); word = rshift(word, 8)
    b1 = band(word, 0xFF); word = rshift(word, 8)
    b2 = band(word, 0xFF); word = rshift(word, 8)
    b3 = band(word, 0xFF)
    return b0, b1, b2, b3
end
function RoCrypt.utils.dword2bytes(i)
    local b4, b5, b6, b7 = RoCrypt.utils.word2bytes(math.floor(i / 0x100000000))
    local b0, b1, b2, b3 = RoCrypt.utils.word2bytes(i)
    return b0, b1, b2, b3, b4, b5, b6, b7
end


function RoCrypt.sha1(message: string)
    local INIT_0 = 0x67452301
    local INIT_1 = 0xEFCDAB89
    local INIT_2 = 0x98BADCFE
    local INIT_3 = 0x10325476
    local INIT_4 = 0xC3D2E1F0

    local APPEND_CHAR = string.char(0x80)
    local INT_32_CAP = 2^32

    ---Packs four 8-bit integers into one 32-bit integer
    local function packUint32(a, b, c, d)
        return lshift(a, 24)+lshift(b, 16)+lshift(c, 8)+d
    end

    ---Unpacks one 32-bit integer into four 8-bit integers
    local function unpackUint32(int)
        return extract(int, 24, 8), extract(int, 16, 8), extract(int, 08, 8), extract(int, 00, 8)
    end

    local function F(t, A, B, C)
        if t <= 19 then
            -- C ~ (A & (B ~ C)) has less ops than (A & B) | (~A & C)
            return bxor(C, band(A, bxor(B, C)))
        elseif t <= 39 then
            return bxor(A, B, C)
        elseif t <= 59 then
            -- A | (B | C) | (B & C) has less ops than (A & B) | (A & C) | (B & C)
            return bor(band(A, bor(B, C)), band(B, C))
        else
            return bxor(A, B, C)
        end
    end

    local function K(t)
        if t <= 19 then
            return 0x5A827999
        elseif t <= 39 then
            return 0x6ED9EBA1
        elseif t <= 59 then
            return 0x8F1BBCDC
        else
            return 0xCA62C1D6
        end
    end

    local function preprocessMessage(message)
        local initMsgLen = #message*8 -- Message length in bits
        local msgLen = initMsgLen+8
        local nulCount = 4 -- This is equivalent to 32 bits.
        message = message..APPEND_CHAR
        while (msgLen+64)%512 ~= 0 do
            nulCount = nulCount+1
            msgLen = msgLen+8
        end
        message = message..string.rep("\0", nulCount)
        message = message..string.char(unpackUint32(initMsgLen))
        return message
    end

    local message = preprocessMessage(message)

    local H0 = INIT_0
    local H1 = INIT_1
    local H2 = INIT_2
    local H3 = INIT_3
    local H4 = INIT_4

    local W = {}
    for chunkStart = 1, #message, 64 do
        local place = chunkStart
        for t = 0, 15 do
            W[t] = packUint32(string.byte(message, place, place+3))
            place = place+4
        end
        for t = 16, 79 do
            W[t] = lrotate(bxor(W[t-3], W[t-8], W[t-14], W[t-16]), 1)
        end

        local A, B, C, D, E = H0, H1, H2, H3, H4

        for t = 0, 79 do
            local TEMP = ( lrotate(A, 5)+F(t, B, C, D)+E+W[t]+K(t) )%INT_32_CAP

            E, D, C, B, A = D, C, lrotate(B, 30), A, TEMP
        end

        H0 = (H0+A)%INT_32_CAP
        H1 = (H1+B)%INT_32_CAP
        H2 = (H2+C)%INT_32_CAP
        H3 = (H3+D)%INT_32_CAP
        H4 = (H4+E)%INT_32_CAP
    end
    local result = string.format("%08x%08x%08x%08x%08x", H0, H1, H2, H3, H4)
    return result


end

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
            c = rshift(c, 1)
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
                p3[j], c = rshift(p3[j], 1) + lshift(c, 23), p3[j] % 2
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
                local r1, r2, mm = Random.new(), Random.new(), lshift(1, (l - 1) % 24)
                local ml = lshift(mm, 1) - 1
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
                n = lshift(r[1], 16) + lshift(r[2], 8) + r[3]
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
                table.insert(a, rshift(a[1], 16))
                table.insert(a, rshift(a[1], 8) % 256)
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

function RoCrypt.base91()
    local CHAR_SET = [[ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%&()*+,./:;<=>?@[]^_`{|}~"]]

    local encode_CharSet = {}
    local decode_CharSet = {}
    for i = 1, 91 do
        encode_CharSet[i-1] = string.sub(CHAR_SET, i, i)
        decode_CharSet[string.sub(CHAR_SET, i, i)] = i-1
    end


    local function encodeBase91(input)
        local output = {}
        local c = 1

        local counter = 0
        local numBits = 0

        for i = 1, #input do
            counter = bor(counter, lshift(string.byte(input, i), numBits))
            numBits = numBits+8
            if numBits > 13 then
                local entry = band(counter, 8191) -- 2^13-1 = 8191
                if entry > 88 then -- Voodoo magic (https://www.reddit.com/r/learnprogramming/comments/8sbb3v/understanding_base91_encoding/e0y85ot/)
                    counter = rshift(counter, 13)
                    numBits = numBits-13
                else
                    entry = band(counter, 16383) -- 2^14-1 = 16383
                    counter = rshift(counter, 14)
                    numBits = numBits-14
                end
                output[c] = encode_CharSet[entry%91]..encode_CharSet[math.floor(entry/91)]
                c = c+1
            end
        end

        if numBits > 0 then
            output[c] = encode_CharSet[counter%91]
            if numBits > 7 or counter > 90 then
                output[c+1] = encode_CharSet[math.floor(counter/91)]
            end
        end

        return table.concat(output)
    end

    local function decodeBase91(input)
        local output = {}
        local c = 1

        local counter = 0
        local numBits = 0
        local entry = -1

        for i = 1, #input do
            if decode_CharSet[string.sub(input, i, i)] then
                if entry == -1 then
                    entry = decode_CharSet[string.sub(input, i, i)]
                else
                    entry = entry+decode_CharSet[string.sub(input, i, i)]*91
                    counter = bor(counter, lshift(entry, numBits))
                    if band(entry, 8191) > 88 then
                        numBits = numBits+13
                    else
                        numBits = numBits+14
                    end

                    while numBits > 7 do
                        output[c] = string.char(counter%256)
                        c = c+1
                        counter = rshift(counter, 8)
                        numBits = numBits-8
                    end
                    entry = -1
                end
            end
        end

        if entry ~= -1 then
            output[c] = string.char(bor(counter, lshift(entry, numBits))%256)
        end

        return table.concat(output)
    end

    return {
        encode = encodeBase91,
        decode = decodeBase91,
    }

end

function RoCrypt.md2(message)
    local queue = RoCrypt.utils.queue()

    local SUBST = {
        0x29, 0x2E, 0x43, 0xC9, 0xA2, 0xD8, 0x7C, 0x01, 0x3D, 0x36, 0x54, 0xA1, 0xEC, 0xF0, 0x06, 0x13,
        0x62, 0xA7, 0x05, 0xF3, 0xC0, 0xC7, 0x73, 0x8C, 0x98, 0x93, 0x2B, 0xD9, 0xBC, 0x4C, 0x82, 0xCA,
        0x1E, 0x9B, 0x57, 0x3C, 0xFD, 0xD4, 0xE0, 0x16, 0x67, 0x42, 0x6F, 0x18, 0x8A, 0x17, 0xE5, 0x12,
        0xBE, 0x4E, 0xC4, 0xD6, 0xDA, 0x9E, 0xDE, 0x49, 0xA0, 0xFB, 0xF5, 0x8E, 0xBB, 0x2F, 0xEE, 0x7A,
        0xA9, 0x68, 0x79, 0x91, 0x15, 0xB2, 0x07, 0x3F, 0x94, 0xC2, 0x10, 0x89, 0x0B, 0x22, 0x5F, 0x21,
        0x80, 0x7F, 0x5D, 0x9A, 0x5A, 0x90, 0x32, 0x27, 0x35, 0x3E, 0xCC, 0xE7, 0xBF, 0xF7, 0x97, 0x03,
        0xFF, 0x19, 0x30, 0xB3, 0x48, 0xA5, 0xB5, 0xD1, 0xD7, 0x5E, 0x92, 0x2A, 0xAC, 0x56, 0xAA, 0xC6,
        0x4F, 0xB8, 0x38, 0xD2, 0x96, 0xA4, 0x7D, 0xB6, 0x76, 0xFC, 0x6B, 0xE2, 0x9C, 0x74, 0x04, 0xF1,
        0x45, 0x9D, 0x70, 0x59, 0x64, 0x71, 0x87, 0x20, 0x86, 0x5B, 0xCF, 0x65, 0xE6, 0x2D, 0xA8, 0x02,
        0x1B, 0x60, 0x25, 0xAD, 0xAE, 0xB0, 0xB9, 0xF6, 0x1C, 0x46, 0x61, 0x69, 0x34, 0x40, 0x7E, 0x0F,
        0x55, 0x47, 0xA3, 0x23, 0xDD, 0x51, 0xAF, 0x3A, 0xC3, 0x5C, 0xF9, 0xCE, 0xBA, 0xC5, 0xEA, 0x26,
        0x2C, 0x53, 0x0D, 0x6E, 0x85, 0x28, 0x84, 0x09, 0xD3, 0xDF, 0xCD, 0xF4, 0x41, 0x81, 0x4D, 0x52,
        0x6A, 0xDC, 0x37, 0xC8, 0x6C, 0xC1, 0xAB, 0xFA, 0x24, 0xE1, 0x7B, 0x08, 0x0C, 0xBD, 0xB1, 0x4A,
        0x78, 0x88, 0x95, 0x8B, 0xE3, 0x63, 0xE8, 0x6D, 0xE9, 0xCB, 0xD5, 0xFE, 0x3B, 0x00, 0x1D, 0x39,
        0xF2, 0xEF, 0xB7, 0x0E, 0x66, 0x58, 0xD0, 0xE4, 0xA6, 0x77, 0x72, 0xF8, 0xEB, 0x75, 0x4B, 0x0A,
        0x31, 0x44, 0x50, 0xB4, 0x8F, 0xED, 0x1F, 0x1A, 0xDB, 0x99, 0x8D, 0x33, 0x9F, 0x11, 0x83, 0x14
    }


    local bytes2word = function(b0, b1, b2, b3)
        local i = b3; i = lshift(i, 8)
        i = bor(i, b2); i = lshift(i, 8)
        i = bor(i, b1); i = lshift(i, 8)
        i = bor(i, b0)
        return i
    end

    local X = {}
    for i = 0, 47 do
        X[i] = 0x00
    end
    local C = {}
    for i = 0, 15 do
        C[i] = 0x00
    end

    local processBlock = function()
        local block = {}
        for i = 0, 15 do
            block[i] = queue.pop()
        end

        for i = 0, 15 do
            X[i + 16] = block[i]
            X[i + 32] = bxor(X[i], block[i]) --mix
        end

        local t
        --update block
        t = 0
        for i = 0, 17 do
            for j = 0, 47 do
                X[j] = bxor(X[j], SUBST[t + 1])
                t = X[j]
            end
            t = (t + i) % 256
        end

        --update checksum
        t = C[15]
        for i = 0, 15 do
            C[i] = bxor(C[i], SUBST[bxor(block[i], t) + 1])
            t = C[i]
        end
    end

    queue.reset()

    X = {}
    for i = 0, 47 do
        X[i] = 0x00
    end

    C = {}
    for i = 0, 15 do
        C[i] = 0x00
    end

    for b in string.gmatch(message, ".") do
        queue.push(string.byte(b))
        if queue.size() >= 16 then
            processBlock()
        end
    end

    local i = 16 - queue.size()
    while queue.size() < 16 do
        queue.push(i)
    end
    processBlock()

    queue.push(C[0])
    queue.push(C[1])
    queue.push(C[2])
    queue.push(C[3])
    queue.push(C[4])
    queue.push(C[5])
    queue.push(C[6])
    queue.push(C[7])
    queue.push(C[8])
    queue.push(C[9])
    queue.push(C[10])
    queue.push(C[11])
    queue.push(C[12])
    queue.push(C[13])
    queue.push(C[14])
    queue.push(C[15])
    processBlock()

    return string.format(
        "%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x",
        X[0], X[1], X[2], X[3], X[4], X[5], X[6], X[7],
        X[8], X[9], X[10], X[11], X[12], X[13], X[14], X[15]
    )
end

function RoCrypt.md4(message: string)

    local Queue = RoCrypt.utils.queue()







    local F = function(x, y, z) return bor(band(x, y), band(bnot(x), z)) end
    local G = function(x, y, z) return bor(band(x, y), bor(band(x, z), band(y, z))) end
    local H = function(x, y, z) return bxor(x, bxor(y, z)) end

    local queue = Queue

     A = 0x67452301
     B = 0xefcdab89
     C = 0x98badcfe
     D = 0x10325476

    local processBlock = function()
        local a = A
        local b = B
        local c = C
        local d = D

        local X = {}

        for i = 0, 15 do
            X[i] = RoCrypt.utils.bytes2word(queue.pop(), queue.pop(), queue.pop(), queue.pop())
        end

        a = lrotate(a + F(b, c, d) + X[ 0],  3)
        d = lrotate(d + F(a, b, c) + X[ 1],  7)
        c = lrotate(c + F(d, a, b) + X[ 2], 11)
        b = lrotate(b + F(c, d, a) + X[ 3], 19)

        a = lrotate(a + F(b, c, d) + X[ 4],  3)
        d = lrotate(d + F(a, b, c) + X[ 5],  7)
        c = lrotate(c + F(d, a, b) + X[ 6], 11)
        b = lrotate(b + F(c, d, a) + X[ 7], 19)

        a = lrotate(a + F(b, c, d) + X[ 8],  3)
        d = lrotate(d + F(a, b, c) + X[ 9],  7)
        c = lrotate(c + F(d, a, b) + X[10], 11)
        b = lrotate(b + F(c, d, a) + X[11], 19)

        a = lrotate(a + F(b, c, d) + X[12],  3)
        d = lrotate(d + F(a, b, c) + X[13],  7)
        c = lrotate(c + F(d, a, b) + X[14], 11)
        b = lrotate(b + F(c, d, a) + X[15], 19)


        a = lrotate(a + G(b, c, d) + X[ 0] + 0x5A827999,  3)
        d = lrotate(d + G(a, b, c) + X[ 4] + 0x5A827999,  5)
        c = lrotate(c + G(d, a, b) + X[ 8] + 0x5A827999,  9)
        b = lrotate(b + G(c, d, a) + X[12] + 0x5A827999, 13)

        a = lrotate(a + G(b, c, d) + X[ 1] + 0x5A827999,  3)
        d = lrotate(d + G(a, b, c) + X[ 5] + 0x5A827999,  5)
        c = lrotate(c + G(d, a, b) + X[ 9] + 0x5A827999,  9)
        b = lrotate(b + G(c, d, a) + X[13] + 0x5A827999, 13)

        a = lrotate(a + G(b, c, d) + X[ 2] + 0x5A827999,  3)
        d = lrotate(d + G(a, b, c) + X[ 6] + 0x5A827999,  5)
        c = lrotate(c + G(d, a, b) + X[10] + 0x5A827999,  9)
        b = lrotate(b + G(c, d, a) + X[14] + 0x5A827999, 13)

        a = lrotate(a + G(b, c, d) + X[ 3] + 0x5A827999,  3)
        d = lrotate(d + G(a, b, c) + X[ 7] + 0x5A827999,  5)
        c = lrotate(c + G(d, a, b) + X[11] + 0x5A827999,  9)
        b = lrotate(b + G(c, d, a) + X[15] + 0x5A827999, 13)


        a = lrotate(a + H(b, c, d) + X[ 0] + 0x6ED9EBA1,  3)
        d = lrotate(d + H(a, b, c) + X[ 8] + 0x6ED9EBA1,  9)
        c = lrotate(c + H(d, a, b) + X[ 4] + 0x6ED9EBA1, 11)
        b = lrotate(b + H(c, d, a) + X[12] + 0x6ED9EBA1, 15)

        a = lrotate(a + H(b, c, d) + X[ 2] + 0x6ED9EBA1,  3)
        d = lrotate(d + H(a, b, c) + X[10] + 0x6ED9EBA1,  9)
        c = lrotate(c + H(d, a, b) + X[ 6] + 0x6ED9EBA1, 11)
        b = lrotate(b + H(c, d, a) + X[14] + 0x6ED9EBA1, 15)

        a = lrotate(a + H(b, c, d) + X[ 1] + 0x6ED9EBA1,  3)
        d = lrotate(d + H(a, b, c) + X[ 9] + 0x6ED9EBA1,  9)
        c = lrotate(c + H(d, a, b) + X[ 5] + 0x6ED9EBA1, 11)
        b = lrotate(b + H(c, d, a) + X[13] + 0x6ED9EBA1, 15)

        a = lrotate(a + H(b, c, d) + X[ 3] + 0x6ED9EBA1,  3)
        d = lrotate(d + H(a, b, c) + X[11] + 0x6ED9EBA1,  9)
        c = lrotate(c + H(d, a, b) + X[ 7] + 0x6ED9EBA1, 11)
        b = lrotate(b + H(c, d, a) + X[15] + 0x6ED9EBA1, 15)


        A = band(A + a, 0xFFFFFFFF)
        B = band(B + b, 0xFFFFFFFF)
        C = band(C + c, 0xFFFFFFFF)
        D = band(D + d, 0xFFFFFFFF)
    end

    queue.reset()

    A = 0x67452301
    B = 0xefcdab89
    C = 0x98badcfe
    D = 0x10325476

    for b in string.gmatch(message, ".") do
        queue.push(string.byte(b))
        if queue.size() >= 64 then processBlock() end
    end

    local bits = queue.getHead() * 8

    queue.push(0x80)
    while ((queue.size() + 7) % 64) < 63 do
        queue.push(0x00)
    end

    local b0, b1, b2, b3, b4, b5, b6, b7 = RoCrypt.utils.dword2bytes(bits)

    queue.push(b0)
    queue.push(b1)
    queue.push(b2)
    queue.push(b3)
    queue.push(b4)
    queue.push(b5)
    queue.push(b6)
    queue.push(b7)

    while queue.size() > 0 do
        processBlock()
    end

    local b0, b1, b2, b3 = RoCrypt.utils.word2bytes(A)
    local b4, b5, b6, b7 = RoCrypt.utils.word2bytes(B)
    local b8, b9, b10, b11 = RoCrypt.utils.word2bytes(C)
    local b12, b13, b14, b15 = RoCrypt.utils.word2bytes(D)

    return string.format("%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x",
        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)
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
                local F = rrotate(band(b, c) + band(-1 - b, d) + a + K[j] + W[j], s) + b
                s = md5_next_shift[s]
                a = d
                d = c
                c = b
                b = F
            end

            s = 27
            for j = 17, 32 do
                local F = rrotate(band(d, b) + band(-1 - d, c) + a + K[j] + W[(5 * j - 4) % 16 + 1], s) + b
                s = md5_next_shift[s]
                a = d
                d = c
                c = b
                b = F
            end

            s = 28
            for j = 33, 48 do
                local F = rrotate(bxor(bxor(b, c), d) + a + K[j] + W[(3 * j + 2) % 16 + 1], s) + b
                s = md5_next_shift[s]
                a = d
                d = c
                c = b
                b = F
            end

            s = 26
            for j = 49, 64 do
                local F = rrotate(bxor(c, bor(b, -1 - d)) + a + K[j] + W[(j * 7 - 7) % 16 + 1], s) + b
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

function RoCrypt.ripemd128(message: string)
 




    local F = function(x, y, z) return bxor(x, bxor(y, z)) end
    local G = function(x, y, z) return bor(band(x, y), band(bnot(x), z)) end
    local H = function(x, y, z) return bxor(bor(x, bnot(y)), z) end
    local I = function(x, y, z) return bor(band(x, z), band(y, bnot(z))) end

    local FF = function(a, b, c, d, x, s)
        a = a + F(b, c, d) + x
        a = lrotate(a, s)
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local GG = function(a, b, c, d, x, s)
        a = a + G(b, c, d) + x + 0x5a827999
        a = lrotate(a, s)
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local HH = function(a, b, c, d, x, s)
        a = a + H(b, c, d) + x + 0x6ed9eba1
        a = lrotate(a, s)
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local II = function(a, b, c, d, x, s)
        a = a + I(b, c, d) + x + 0x8f1bbcdc
        a = lrotate(a, s)
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local FFF = function(a, b, c, d, x, s)
        a = a + F(b, c, d) + x
        a = lrotate(a, s)
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local GGG = function(a, b, c, d, x, s)
        a = a + G(b, c, d) + x + 0x6d703ef3
        a = lrotate(a, s)
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local HHH = function(a, b, c, d, x, s)
        a = a + H(b, c, d) + x + 0x5c4dd124
        a = lrotate(a, s)
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local III = function(a, b, c, d, x, s)
        a = a + I(b, c, d) + x + 0x50a28be6
        a = lrotate(a, s)
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local queue = RoCrypt.utils.queue()

    local processBlock = function()
        local aa, bb, cc, dd = A, B, C, D
        local aaa, bbb, ccc, ddd = A, B, C, D

        local X = {}

        for i = 0, 15 do
            X[i] = RoCrypt.utils.bytes2word(queue.pop(), queue.pop(), queue.pop(), queue.pop())
        end

        aa = FF(aa, bb, cc, dd, X[ 0], 11)
        dd = FF(dd, aa, bb, cc, X[ 1], 14)
        cc = FF(cc, dd, aa, bb, X[ 2], 15)
        bb = FF(bb, cc, dd, aa, X[ 3], 12)
        aa = FF(aa, bb, cc, dd, X[ 4],  5)
        dd = FF(dd, aa, bb, cc, X[ 5],  8)
        cc = FF(cc, dd, aa, bb, X[ 6],  7)
        bb = FF(bb, cc, dd, aa, X[ 7],  9)
        aa = FF(aa, bb, cc, dd, X[ 8], 11)
        dd = FF(dd, aa, bb, cc, X[ 9], 13)
        cc = FF(cc, dd, aa, bb, X[10], 14)
        bb = FF(bb, cc, dd, aa, X[11], 15)
        aa = FF(aa, bb, cc, dd, X[12],  6)
        dd = FF(dd, aa, bb, cc, X[13],  7)
        cc = FF(cc, dd, aa, bb, X[14],  9)
        bb = FF(bb, cc, dd, aa, X[15],  8)

        aa = GG(aa, bb, cc, dd, X[ 7],  7)
        dd = GG(dd, aa, bb, cc, X[ 4],  6)
        cc = GG(cc, dd, aa, bb, X[13],  8)
        bb = GG(bb, cc, dd, aa, X[ 1], 13)
        aa = GG(aa, bb, cc, dd, X[10], 11)
        dd = GG(dd, aa, bb, cc, X[ 6],  9)
        cc = GG(cc, dd, aa, bb, X[15],  7)
        bb = GG(bb, cc, dd, aa, X[ 3], 15)
        aa = GG(aa, bb, cc, dd, X[12],  7)
        dd = GG(dd, aa, bb, cc, X[ 0], 12)
        cc = GG(cc, dd, aa, bb, X[ 9], 15)
        bb = GG(bb, cc, dd, aa, X[ 5],  9)
        aa = GG(aa, bb, cc, dd, X[ 2], 11)
        dd = GG(dd, aa, bb, cc, X[14],  7)
        cc = GG(cc, dd, aa, bb, X[11], 13)
        bb = GG(bb, cc, dd, aa, X[ 8], 12)

        aa = HH(aa, bb, cc, dd, X[ 3], 11)
        dd = HH(dd, aa, bb, cc, X[10], 13)
        cc = HH(cc, dd, aa, bb, X[14],  6)
        bb = HH(bb, cc, dd, aa, X[ 4],  7)
        aa = HH(aa, bb, cc, dd, X[ 9], 14)
        dd = HH(dd, aa, bb, cc, X[15],  9)
        cc = HH(cc, dd, aa, bb, X[ 8], 13)
        bb = HH(bb, cc, dd, aa, X[ 1], 15)
        aa = HH(aa, bb, cc, dd, X[ 2], 14)
        dd = HH(dd, aa, bb, cc, X[ 7],  8)
        cc = HH(cc, dd, aa, bb, X[ 0], 13)
        bb = HH(bb, cc, dd, aa, X[ 6],  6)
        aa = HH(aa, bb, cc, dd, X[13],  5)
        dd = HH(dd, aa, bb, cc, X[11], 12)
        cc = HH(cc, dd, aa, bb, X[ 5],  7)
        bb = HH(bb, cc, dd, aa, X[12],  5)

        aa = II(aa, bb, cc, dd, X[ 1], 11)
        dd = II(dd, aa, bb, cc, X[ 9], 12)
        cc = II(cc, dd, aa, bb, X[11], 14)
        bb = II(bb, cc, dd, aa, X[10], 15)
        aa = II(aa, bb, cc, dd, X[ 0], 14)
        dd = II(dd, aa, bb, cc, X[ 8], 15)
        cc = II(cc, dd, aa, bb, X[12],  9)
        bb = II(bb, cc, dd, aa, X[ 4],  8)
        aa = II(aa, bb, cc, dd, X[13],  9)
        dd = II(dd, aa, bb, cc, X[ 3], 14)
        cc = II(cc, dd, aa, bb, X[ 7],  5)
        bb = II(bb, cc, dd, aa, X[15],  6)
        aa = II(aa, bb, cc, dd, X[14],  8)
        dd = II(dd, aa, bb, cc, X[ 5],  6)
        cc = II(cc, dd, aa, bb, X[ 6],  5)
        bb = II(bb, cc, dd, aa, X[ 2], 12)

        aaa = III(aaa, bbb, ccc, ddd, X[ 5],  8)
        ddd = III(ddd, aaa, bbb, ccc, X[14],  9)
        ccc = III(ccc, ddd, aaa, bbb, X[ 7],  9)
        bbb = III(bbb, ccc, ddd, aaa, X[ 0], 11)
        aaa = III(aaa, bbb, ccc, ddd, X[ 9], 13)
        ddd = III(ddd, aaa, bbb, ccc, X[ 2], 15)
        ccc = III(ccc, ddd, aaa, bbb, X[11], 15)
        bbb = III(bbb, ccc, ddd, aaa, X[ 4],  5)
        aaa = III(aaa, bbb, ccc, ddd, X[13],  7)
        ddd = III(ddd, aaa, bbb, ccc, X[ 6],  7)
        ccc = III(ccc, ddd, aaa, bbb, X[15],  8)
        bbb = III(bbb, ccc, ddd, aaa, X[ 8], 11)
        aaa = III(aaa, bbb, ccc, ddd, X[ 1], 14)
        ddd = III(ddd, aaa, bbb, ccc, X[10], 14)
        ccc = III(ccc, ddd, aaa, bbb, X[ 3], 12)
        bbb = III(bbb, ccc, ddd, aaa, X[12],  6)

        aaa = HHH(aaa, bbb, ccc, ddd, X[ 6],  9)
        ddd = HHH(ddd, aaa, bbb, ccc, X[11], 13)
        ccc = HHH(ccc, ddd, aaa, bbb, X[ 3], 15)
        bbb = HHH(bbb, ccc, ddd, aaa, X[ 7],  7)
        aaa = HHH(aaa, bbb, ccc, ddd, X[ 0], 12)
        ddd = HHH(ddd, aaa, bbb, ccc, X[13],  8)
        ccc = HHH(ccc, ddd, aaa, bbb, X[ 5],  9)
        bbb = HHH(bbb, ccc, ddd, aaa, X[10], 11)
        aaa = HHH(aaa, bbb, ccc, ddd, X[14],  7)
        ddd = HHH(ddd, aaa, bbb, ccc, X[15],  7)
        ccc = HHH(ccc, ddd, aaa, bbb, X[ 8], 12)
        bbb = HHH(bbb, ccc, ddd, aaa, X[12],  7)
        aaa = HHH(aaa, bbb, ccc, ddd, X[ 4],  6)
        ddd = HHH(ddd, aaa, bbb, ccc, X[ 9], 15)
        ccc = HHH(ccc, ddd, aaa, bbb, X[ 1], 13)
        bbb = HHH(bbb, ccc, ddd, aaa, X[ 2], 11)

        aaa = GGG(aaa, bbb, ccc, ddd, X[15],  9)
        ddd = GGG(ddd, aaa, bbb, ccc, X[ 5],  7)
        ccc = GGG(ccc, ddd, aaa, bbb, X[ 1], 15)
        bbb = GGG(bbb, ccc, ddd, aaa, X[ 3], 11)
        aaa = GGG(aaa, bbb, ccc, ddd, X[ 7],  8)
        ddd = GGG(ddd, aaa, bbb, ccc, X[14],  6)
        ccc = GGG(ccc, ddd, aaa, bbb, X[ 6],  6)
        bbb = GGG(bbb, ccc, ddd, aaa, X[ 9], 14)
        aaa = GGG(aaa, bbb, ccc, ddd, X[11], 12)
        ddd = GGG(ddd, aaa, bbb, ccc, X[ 8], 13)
        ccc = GGG(ccc, ddd, aaa, bbb, X[12],  5)
        bbb = GGG(bbb, ccc, ddd, aaa, X[ 2], 14)
        aaa = GGG(aaa, bbb, ccc, ddd, X[10], 13)
        ddd = GGG(ddd, aaa, bbb, ccc, X[ 0], 13)
        ccc = GGG(ccc, ddd, aaa, bbb, X[ 4],  7)
        bbb = GGG(bbb, ccc, ddd, aaa, X[13],  5)

        aaa = FFF(aaa, bbb, ccc, ddd, X[ 8], 15)
        ddd = FFF(ddd, aaa, bbb, ccc, X[ 6],  5)
        ccc = FFF(ccc, ddd, aaa, bbb, X[ 4],  8)
        bbb = FFF(bbb, ccc, ddd, aaa, X[ 1], 11) aaa = FFF(aaa, bbb, ccc, ddd, X[ 3], 14)
        ddd = FFF(ddd, aaa, bbb, ccc, X[11], 14)
        ccc = FFF(ccc, ddd, aaa, bbb, X[15],  6)
        bbb = FFF(bbb, ccc, ddd, aaa, X[ 0], 14)
        aaa = FFF(aaa, bbb, ccc, ddd, X[ 5],  6)
        ddd = FFF(ddd, aaa, bbb, ccc, X[12],  9)
        ccc = FFF(ccc, ddd, aaa, bbb, X[ 2], 12)
        bbb = FFF(bbb, ccc, ddd, aaa, X[13],  9)
        aaa = FFF(aaa, bbb, ccc, ddd, X[ 9], 12)
        ddd = FFF(ddd, aaa, bbb, ccc, X[ 7],  5)
        ccc = FFF(ccc, ddd, aaa, bbb, X[10], 15)
        bbb = FFF(bbb, ccc, ddd, aaa, X[14],  8)


        A, B, C, D = band(B + cc + ddd, 0xFFFFFFFF), band(C + dd + aaa, 0xFFFFFFFF), band(D + aa + bbb, 0xFFFFFFFF), band(A + bb + ccc, 0xFFFFFFFF)
    end

    local init = function()
        queue.reset()

        A = 0x67452301
        B = 0xefcdab89
        C = 0x98badcfe
        D = 0x10325476
    end

    local update = function(bytes)
        for i = 1, #bytes do
            queue.push(bytes:byte(i))
            if queue.size() >= 64 then processBlock() end
        end
    end

    local finish = function()
        local bits = queue.getHead() * 8

        queue.push(0x80)

        while ((queue.size() + 7) % 64) < 63 do
            queue.push(0x00)
        end

        local b0, b1, b2, b3, b4, b5, b6, b7 = RoCrypt.utils.dword2bytes(bits)

        queue.push(b0)
        queue.push(b1)
        queue.push(b2)
        queue.push(b3)
        queue.push(b4)
        queue.push(b5)
        queue.push(b6)
        queue.push(b7)

        while queue.size() > 0 do
            processBlock()
        end
    end

    local asHex = function()
        local b0, b1, b2, b3 = RoCrypt.utils.word2bytes(A)
        local b4, b5, b6, b7 = RoCrypt.utils.word2bytes(B)
        local b8, b9, b10, b11 = RoCrypt.utils.word2bytes(C)
        local b12, b13, b14, b15 = RoCrypt.utils.word2bytes(D)

        local fmt = "%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x"

        return string.format(fmt,
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
            b10, b11, b12, b13, b14, b15)
    end

    init()
    update(message)
    finish()

    return asHex()
end

function RoCrypt.ripemd160(message: string)





    local F = function(x, y, z) return bxor(x, bxor(y, z)) end
    local G = function(x, y, z) return bor(band(x, y), band(bnot(x), z)) end
    local H = function(x, y, z) return bxor(bor(x, bnot(y)), z) end
    local I = function(x, y, z) return bor(band(x, z), band(y, bnot(z))) end
    local J = function(x, y, z) return bxor(x, bor(y, bnot(z))) end

    local FF = function(a, b, c, d, e, x, s)
        a = a + F(b, c, d) + x
        a = lrotate(a, s) + e
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local GG = function(a, b, c, d, e, x, s)
        a = a + G(b, c, d) + x + 0x5a827999
        a = lrotate(a, s) + e
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local HH = function(a, b, c, d, e, x, s)
        a = a + H(b, c, d) + x + 0x6ed9eba1
        a = lrotate(a, s) + e
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local II = function(a, b, c, d, e, x, s)
        a = a + I(b, c, d) + x + 0x8f1bbcdc
        a = lrotate(a, s) + e
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local JJ = function(a, b, c, d, e, x, s)
        a = a + J(b, c, d) + x + 0xa953fd4e
        a = lrotate(a, s) + e
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local FFF = function(a, b, c, d, e, x, s)
        a = a + F(b, c, d) + x
        a = lrotate(a, s) + e
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local GGG = function(a, b, c, d, e, x, s)
        a = a + G(b, c, d) + x + 0x7a6d76e9
        a = lrotate(a, s) + e
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local HHH = function(a, b, c, d, e, x, s)
        a = a + H(b, c, d) + x + 0x6d703ef3
        a = lrotate(a, s) + e
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local III = function(a, b, c, d, e, x, s)
        a = a + I(b, c, d) + x + 0x5c4dd124
        a = lrotate(a, s) + e
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local JJJ = function(a, b, c, d, e, x, s)
        a = a + J(b, c, d) + x + 0x50a28be6
        a = lrotate(a, s) + e
        a = band(a, 0xFFFFFFFF)
        return a
    end

    local queue = RoCrypt.utils.queue()

    local processBlock = function()

        local aa, bb, cc, dd, ee = A, B, C, D, E
        local aaa, bbb, ccc, ddd, eee = A, B, C, D, E

        local X = {}

        for i = 0, 15 do
            X[i] = RoCrypt.utils.bytes2word(queue.pop(), queue.pop(), queue.pop(), queue.pop())
        end

        aa, cc = FF(aa, bb, cc, dd, ee, X[ 0], 11), lrotate(cc, 10)
        ee, bb = FF(ee, aa, bb, cc, dd, X[ 1], 14), lrotate(bb, 10)
        dd, aa = FF(dd, ee, aa, bb, cc, X[ 2], 15), lrotate(aa, 10)
        cc, ee = FF(cc, dd, ee, aa, bb, X[ 3], 12), lrotate(ee, 10)
        bb, dd = FF(bb, cc, dd, ee, aa, X[ 4],  5), lrotate(dd, 10)
        aa, cc = FF(aa, bb, cc, dd, ee, X[ 5],  8), lrotate(cc, 10)
        ee, bb = FF(ee, aa, bb, cc, dd, X[ 6],  7), lrotate(bb, 10)
        dd, aa = FF(dd, ee, aa, bb, cc, X[ 7],  9), lrotate(aa, 10)
        cc, ee = FF(cc, dd, ee, aa, bb, X[ 8], 11), lrotate(ee, 10)
        bb, dd = FF(bb, cc, dd, ee, aa, X[ 9], 13), lrotate(dd, 10)
        aa, cc = FF(aa, bb, cc, dd, ee, X[10], 14), lrotate(cc, 10)
        ee, bb = FF(ee, aa, bb, cc, dd, X[11], 15), lrotate(bb, 10)
        dd, aa = FF(dd, ee, aa, bb, cc, X[12],  6), lrotate(aa, 10)
        cc, ee = FF(cc, dd, ee, aa, bb, X[13],  7), lrotate(ee, 10)
        bb, dd = FF(bb, cc, dd, ee, aa, X[14],  9), lrotate(dd, 10)
        aa, cc = FF(aa, bb, cc, dd, ee, X[15],  8), lrotate(cc, 10)

        ee, bb = GG(ee, aa, bb, cc, dd, X[ 7],  7), lrotate(bb, 10)
        dd, aa = GG(dd, ee, aa, bb, cc, X[ 4],  6), lrotate(aa, 10)
        cc, ee = GG(cc, dd, ee, aa, bb, X[13],  8), lrotate(ee, 10)
        bb, dd = GG(bb, cc, dd, ee, aa, X[ 1], 13), lrotate(dd, 10)
        aa, cc = GG(aa, bb, cc, dd, ee, X[10], 11), lrotate(cc, 10)
        ee, bb = GG(ee, aa, bb, cc, dd, X[ 6],  9), lrotate(bb, 10)
        dd, aa = GG(dd, ee, aa, bb, cc, X[15],  7), lrotate(aa, 10)
        cc, ee = GG(cc, dd, ee, aa, bb, X[ 3], 15), lrotate(ee, 10)
        bb, dd = GG(bb, cc, dd, ee, aa, X[12],  7), lrotate(dd, 10)
        aa, cc = GG(aa, bb, cc, dd, ee, X[ 0], 12), lrotate(cc, 10)
        ee, bb = GG(ee, aa, bb, cc, dd, X[ 9], 15), lrotate(bb, 10)
        dd, aa = GG(dd, ee, aa, bb, cc, X[ 5],  9), lrotate(aa, 10)
        cc, ee = GG(cc, dd, ee, aa, bb, X[ 2], 11), lrotate(ee, 10)
        bb, dd = GG(bb, cc, dd, ee, aa, X[14],  7), lrotate(dd, 10)
        aa, cc = GG(aa, bb, cc, dd, ee, X[11], 13), lrotate(cc, 10)
        ee, bb = GG(ee, aa, bb, cc, dd, X[ 8], 12), lrotate(bb, 10)

        dd, aa = HH(dd, ee, aa, bb, cc, X[ 3], 11), lrotate(aa, 10)
        cc, ee = HH(cc, dd, ee, aa, bb, X[10], 13), lrotate(ee, 10)
        bb, dd = HH(bb, cc, dd, ee, aa, X[14],  6), lrotate(dd, 10)
        aa, cc = HH(aa, bb, cc, dd, ee, X[ 4],  7), lrotate(cc, 10)
        ee, bb = HH(ee, aa, bb, cc, dd, X[ 9], 14), lrotate(bb, 10)
        dd, aa = HH(dd, ee, aa, bb, cc, X[15],  9), lrotate(aa, 10)
        cc, ee = HH(cc, dd, ee, aa, bb, X[ 8], 13), lrotate(ee, 10)
        bb, dd = HH(bb, cc, dd, ee, aa, X[ 1], 15), lrotate(dd, 10)
        aa, cc = HH(aa, bb, cc, dd, ee, X[ 2], 14), lrotate(cc, 10)
        ee, bb = HH(ee, aa, bb, cc, dd, X[ 7],  8), lrotate(bb, 10)
        dd, aa = HH(dd, ee, aa, bb, cc, X[ 0], 13), lrotate(aa, 10)
        cc, ee = HH(cc, dd, ee, aa, bb, X[ 6],  6), lrotate(ee, 10)
        bb, dd = HH(bb, cc, dd, ee, aa, X[13],  5), lrotate(dd, 10)
        aa, cc = HH(aa, bb, cc, dd, ee, X[11], 12), lrotate(cc, 10)
        ee, bb = HH(ee, aa, bb, cc, dd, X[ 5],  7), lrotate(bb, 10)
        dd, aa = HH(dd, ee, aa, bb, cc, X[12],  5), lrotate(aa, 10)

        cc, ee = II(cc, dd, ee, aa, bb, X[ 1], 11), lrotate(ee, 10)
        bb, dd = II(bb, cc, dd, ee, aa, X[ 9], 12), lrotate(dd, 10)
        aa, cc = II(aa, bb, cc, dd, ee, X[11], 14), lrotate(cc, 10)
        ee, bb = II(ee, aa, bb, cc, dd, X[10], 15), lrotate(bb, 10)
        dd, aa = II(dd, ee, aa, bb, cc, X[ 0], 14), lrotate(aa, 10)
        cc, ee = II(cc, dd, ee, aa, bb, X[ 8], 15), lrotate(ee, 10)
        bb, dd = II(bb, cc, dd, ee, aa, X[12],  9), lrotate(dd, 10)
        aa, cc = II(aa, bb, cc, dd, ee, X[ 4],  8), lrotate(cc, 10)
        ee, bb = II(ee, aa, bb, cc, dd, X[13],  9), lrotate(bb, 10)
        dd, aa = II(dd, ee, aa, bb, cc, X[ 3], 14), lrotate(aa, 10)
        cc, ee = II(cc, dd, ee, aa, bb, X[ 7],  5), lrotate(ee, 10)
        bb, dd = II(bb, cc, dd, ee, aa, X[15],  6), lrotate(dd, 10)
        aa, cc = II(aa, bb, cc, dd, ee, X[14],  8), lrotate(cc, 10)
        ee, bb = II(ee, aa, bb, cc, dd, X[ 5],  6), lrotate(bb, 10)
        dd, aa = II(dd, ee, aa, bb, cc, X[ 6],  5), lrotate(aa, 10)
        cc, ee = II(cc, dd, ee, aa, bb, X[ 2], 12), lrotate(ee, 10)

        bb, dd = JJ(bb, cc, dd, ee, aa, X[ 4],  9), lrotate(dd, 10)
        aa, cc = JJ(aa, bb, cc, dd, ee, X[ 0], 15), lrotate(cc, 10)
        ee, bb = JJ(ee, aa, bb, cc, dd, X[ 5],  5), lrotate(bb, 10)
        dd, aa = JJ(dd, ee, aa, bb, cc, X[ 9], 11), lrotate(aa, 10)
        cc, ee = JJ(cc, dd, ee, aa, bb, X[ 7],  6), lrotate(ee, 10)
        bb, dd = JJ(bb, cc, dd, ee, aa, X[12],  8), lrotate(dd, 10)
        aa, cc = JJ(aa, bb, cc, dd, ee, X[ 2], 13), lrotate(cc, 10)
        ee, bb = JJ(ee, aa, bb, cc, dd, X[10], 12), lrotate(bb, 10)
        dd, aa = JJ(dd, ee, aa, bb, cc, X[14],  5), lrotate(aa, 10)
        cc, ee = JJ(cc, dd, ee, aa, bb, X[ 1], 12), lrotate(ee, 10)
        bb, dd = JJ(bb, cc, dd, ee, aa, X[ 3], 13), lrotate(dd, 10)
        aa, cc = JJ(aa, bb, cc, dd, ee, X[ 8], 14), lrotate(cc, 10)
        ee, bb = JJ(ee, aa, bb, cc, dd, X[11], 11), lrotate(bb, 10)
        dd, aa = JJ(dd, ee, aa, bb, cc, X[ 6],  8), lrotate(aa, 10)
        cc, ee = JJ(cc, dd, ee, aa, bb, X[15],  5), lrotate(ee, 10)
        bb, dd = JJ(bb, cc, dd, ee, aa, X[13],  6), lrotate(dd, 10)
        aaa, ccc = JJJ(aaa, bbb, ccc, ddd, eee, X[ 5],  8), lrotate(ccc, 10)
        eee, bbb = JJJ(eee, aaa, bbb, ccc, ddd, X[14],  9), lrotate(bbb, 10)
        ddd, aaa = JJJ(ddd, eee, aaa, bbb, ccc, X[ 7],  9), lrotate(aaa, 10)
        ccc, eee = JJJ(ccc, ddd, eee, aaa, bbb, X[ 0], 11), lrotate(eee, 10)
        bbb, ddd = JJJ(bbb, ccc, ddd, eee, aaa, X[ 9], 13), lrotate(ddd, 10)
        aaa, ccc = JJJ(aaa, bbb, ccc, ddd, eee, X[ 2], 15), lrotate(ccc, 10)
        eee, bbb = JJJ(eee, aaa, bbb, ccc, ddd, X[11], 15), lrotate(bbb, 10)
        ddd, aaa = JJJ(ddd, eee, aaa, bbb, ccc, X[ 4],  5), lrotate(aaa, 10)
        ccc, eee = JJJ(ccc, ddd, eee, aaa, bbb, X[13],  7), lrotate(eee, 10)
        bbb, ddd = JJJ(bbb, ccc, ddd, eee, aaa, X[ 6],  7), lrotate(ddd, 10)
        aaa, ccc = JJJ(aaa, bbb, ccc, ddd, eee, X[15],  8), lrotate(ccc, 10)
        eee, bbb = JJJ(eee, aaa, bbb, ccc, ddd, X[ 8], 11), lrotate(bbb, 10)
        ddd, aaa = JJJ(ddd, eee, aaa, bbb, ccc, X[ 1], 14), lrotate(aaa, 10)
        ccc, eee = JJJ(ccc, ddd, eee, aaa, bbb, X[10], 14), lrotate(eee, 10)
        bbb, ddd = JJJ(bbb, ccc, ddd, eee, aaa, X[ 3], 12), lrotate(ddd, 10)
        aaa, ccc = JJJ(aaa, bbb, ccc, ddd, eee, X[12],  6), lrotate(ccc, 10)

        eee, bbb = III(eee, aaa, bbb, ccc, ddd, X[ 6],  9), lrotate(bbb, 10)
        ddd, aaa = III(ddd, eee, aaa, bbb, ccc, X[11], 13), lrotate(aaa, 10)
        ccc, eee = III(ccc, ddd, eee, aaa, bbb, X[ 3], 15), lrotate(eee, 10)
        bbb, ddd = III(bbb, ccc, ddd, eee, aaa, X[ 7],  7), lrotate(ddd, 10)
        aaa, ccc = III(aaa, bbb, ccc, ddd, eee, X[ 0], 12), lrotate(ccc, 10)
        eee, bbb = III(eee, aaa, bbb, ccc, ddd, X[13],  8), lrotate(bbb, 10)
        ddd, aaa = III(ddd, eee, aaa, bbb, ccc, X[ 5],  9), lrotate(aaa, 10)
        ccc, eee = III(ccc, ddd, eee, aaa, bbb, X[10], 11), lrotate(eee, 10)
        bbb, ddd = III(bbb, ccc, ddd, eee, aaa, X[14],  7), lrotate(ddd, 10)
        aaa, ccc = III(aaa, bbb, ccc, ddd, eee, X[15],  7), lrotate(ccc, 10)
        eee, bbb = III(eee, aaa, bbb, ccc, ddd, X[ 8], 12), lrotate(bbb, 10)
        ddd, aaa = III(ddd, eee, aaa, bbb, ccc, X[12],  7), lrotate(aaa, 10)
        ccc, eee = III(ccc, ddd, eee, aaa, bbb, X[ 4],  6), lrotate(eee, 10)
        bbb, ddd = III(bbb, ccc, ddd, eee, aaa, X[ 9], 15), lrotate(ddd, 10)
        aaa, ccc = III(aaa, bbb, ccc, ddd, eee, X[ 1], 13), lrotate(ccc, 10)
        eee, bbb = III(eee, aaa, bbb, ccc, ddd, X[ 2], 11), lrotate(bbb, 10)

        ddd, aaa = HHH(ddd, eee, aaa, bbb, ccc, X[15],  9), lrotate(aaa, 10)
        ccc, eee = HHH(ccc, ddd, eee, aaa, bbb, X[ 5],  7), lrotate(eee, 10)
        bbb, ddd = HHH(bbb, ccc, ddd, eee, aaa, X[ 1], 15), lrotate(ddd, 10)
        aaa, ccc = HHH(aaa, bbb, ccc, ddd, eee, X[ 3], 11), lrotate(ccc, 10)
        eee, bbb = HHH(eee, aaa, bbb, ccc, ddd, X[ 7],  8), lrotate(bbb, 10)
        ddd, aaa = HHH(ddd, eee, aaa, bbb, ccc, X[14],  6), lrotate(aaa, 10)
        ccc, eee = HHH(ccc, ddd, eee, aaa, bbb, X[ 6],  6), lrotate(eee, 10)
        bbb, ddd = HHH(bbb, ccc, ddd, eee, aaa, X[ 9], 14), lrotate(ddd, 10)
        aaa, ccc = HHH(aaa, bbb, ccc, ddd, eee, X[11], 12), lrotate(ccc, 10)
        eee, bbb = HHH(eee, aaa, bbb, ccc, ddd, X[ 8], 13), lrotate(bbb, 10)
        ddd, aaa = HHH(ddd, eee, aaa, bbb, ccc, X[12],  5), lrotate(aaa, 10)
        ccc, eee = HHH(ccc, ddd, eee, aaa, bbb, X[ 2], 14), lrotate(eee, 10)
        bbb, ddd = HHH(bbb, ccc, ddd, eee, aaa, X[10], 13), lrotate(ddd, 10)
        aaa, ccc = HHH(aaa, bbb, ccc, ddd, eee, X[ 0], 13), lrotate(ccc, 10)
        eee, bbb = HHH(eee, aaa, bbb, ccc, ddd, X[ 4],  7), lrotate(bbb, 10)
        ddd, aaa = HHH(ddd, eee, aaa, bbb, ccc, X[13],  5), lrotate(aaa, 10)

        ccc, eee = GGG(ccc, ddd, eee, aaa, bbb, X[ 8], 15), lrotate(eee, 10)
        bbb, ddd = GGG(bbb, ccc, ddd, eee, aaa, X[ 6],  5), lrotate(ddd, 10)
        aaa, ccc = GGG(aaa, bbb, ccc, ddd, eee, X[ 4],  8), lrotate(ccc, 10)
        eee, bbb = GGG(eee, aaa, bbb, ccc, ddd, X[ 1], 11), lrotate(bbb, 10)
        ddd, aaa = GGG(ddd, eee, aaa, bbb, ccc, X[ 3], 14), lrotate(aaa, 10)
        ccc, eee = GGG(ccc, ddd, eee, aaa, bbb, X[11], 14), lrotate(eee, 10)
        bbb, ddd = GGG(bbb, ccc, ddd, eee, aaa, X[15],  6), lrotate(ddd, 10)
        aaa, ccc = GGG(aaa, bbb, ccc, ddd, eee, X[ 0], 14), lrotate(ccc, 10)
        eee, bbb = GGG(eee, aaa, bbb, ccc, ddd, X[ 5],  6), lrotate(bbb, 10)
        ddd, aaa = GGG(ddd, eee, aaa, bbb, ccc, X[12],  9), lrotate(aaa, 10)
        ccc, eee = GGG(ccc, ddd, eee, aaa, bbb, X[ 2], 12), lrotate(eee, 10)
        bbb, ddd = GGG(bbb, ccc, ddd, eee, aaa, X[13],  9), lrotate(ddd, 10)
        aaa, ccc = GGG(aaa, bbb, ccc, ddd, eee, X[ 9], 12), lrotate(ccc, 10)
        eee, bbb = GGG(eee, aaa, bbb, ccc, ddd, X[ 7],  5), lrotate(bbb, 10)
        ddd, aaa = GGG(ddd, eee, aaa, bbb, ccc, X[10], 15), lrotate(aaa, 10)
        ccc, eee = GGG(ccc, ddd, eee, aaa, bbb, X[14],  8), lrotate(eee, 10)

        bbb, ddd = FFF(bbb, ccc, ddd, eee, aaa, X[12] ,  8), lrotate(ddd, 10)
        aaa, ccc = FFF(aaa, bbb, ccc, ddd, eee, X[15] ,  5), lrotate(ccc, 10)
        eee, bbb = FFF(eee, aaa, bbb, ccc, ddd, X[10] , 12), lrotate(bbb, 10)
        ddd, aaa = FFF(ddd, eee, aaa, bbb, ccc, X[ 4] ,  9), lrotate(aaa, 10)
        ccc, eee = FFF(ccc, ddd, eee, aaa, bbb, X[ 1] , 12), lrotate(eee, 10)
        bbb, ddd = FFF(bbb, ccc, ddd, eee, aaa, X[ 5] ,  5), lrotate(ddd, 10)
        aaa, ccc = FFF(aaa, bbb, ccc, ddd, eee, X[ 8] , 14), lrotate(ccc, 10)
        eee, bbb = FFF(eee, aaa, bbb, ccc, ddd, X[ 7] ,  6), lrotate(bbb, 10)
        ddd, aaa = FFF(ddd, eee, aaa, bbb, ccc, X[ 6] ,  8), lrotate(aaa, 10)
        ccc, eee = FFF(ccc, ddd, eee, aaa, bbb, X[ 2] , 13), lrotate(eee, 10)
        bbb, ddd = FFF(bbb, ccc, ddd, eee, aaa, X[13] ,  6), lrotate(ddd, 10)
        aaa, ccc = FFF(aaa, bbb, ccc, ddd, eee, X[14] ,  5), lrotate(ccc, 10)
        eee, bbb = FFF(eee, aaa, bbb, ccc, ddd, X[ 0] , 15), lrotate(bbb, 10)
        ddd, aaa = FFF(ddd, eee, aaa, bbb, ccc, X[ 3] , 13), lrotate(aaa, 10)
        ccc, eee = FFF(ccc, ddd, eee, aaa, bbb, X[ 9] , 11), lrotate(eee, 10)
        bbb, ddd = FFF(bbb, ccc, ddd, eee, aaa, X[11] , 11), lrotate(ddd, 10)

        A, B, C, D, E = band(B + cc + ddd, 0xFFFFFFFF), band(C + dd + eee, 0xFFFFFFFF), band(D + ee + aaa, 0xFFFFFFFF), band(E + aa + bbb, 0xFFFFFFFF), band(A + bb + ccc, 0xFFFFFFFF)
    end

    local init = function()
        queue.reset()

        A = 0x67452301
        B = 0xefcdab89
        C = 0x98badcfe
        D = 0x10325476
        E = 0xc3d2e1f0
    end

    local update = function(bytes)
        for i = 1, #bytes do
            queue.push(bytes:byte(i))
            if queue.size() >= 64 then processBlock() end
        end
    end

    local finish = function()
        local bits = queue.getHead() * 8

        queue.push(0x80)

        while ((queue.size() + 7) % 64) < 63 do
            queue.push(0x00)
        end

        local b0, b1, b2, b3, b4, b5, b6, b7 = RoCrypt.utils.dword2bytes(bits)

        queue.push(b0)
        queue.push(b1)
        queue.push(b2)
        queue.push(b3)
        queue.push(b4)
        queue.push(b5)
        queue.push(b6)
        queue.push(b7)

        while queue.size() > 0 do
            processBlock()
        end
    end



    local asHex = function()
        local b0, b1, b2, b3 = RoCrypt.utils.word2bytes(A)
        local b4, b5, b6, b7 = RoCrypt.utils.word2bytes(B)
        local b8, b9, b10, b11 = RoCrypt.utils.word2bytes(C)
        local b12, b13, b14, b15 = RoCrypt.utils.word2bytes(D)
        local b16, b17, b18, b19 = RoCrypt.utils.word2bytes(E)

        local fmt = "%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x"

        return string.format(fmt,
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
            b10, b11, b12, b13, b14, b15, b16, b17, b18, b19)
    end



    init()
    update(message)
    finish()

    return asHex()

end

function RoCrypt.aes(message: any?)
    --[[
ADVANCED ENCRYPTION STANDARD (AES)

Implementation of secure symmetric-key encryption specifically in Luau
Includes ECB, CBC, PCBC, CFB, OFB and CTR modes without padding.
Made by @RobloxGamerPro200007 (verify the original asset)

MORE INFORMATION: https://devforum.roblox.com/t/advanced-encryption-standard-in-luau/2009120
]]

    -- SUBSTITUTION BOXES
    local s_box 	= { 99, 124, 119, 123, 242, 107, 111, 197,  48,   1, 103,  43, 254, 215, 171, 118, 202,
        130, 201, 125, 250,  89,  71, 240, 173, 212, 162, 175, 156, 164, 114, 192, 183, 253, 147,  38,  54,
        63, 247, 204,  52, 165, 229, 241, 113, 216,  49,  21,   4, 199,  35, 195,  24, 150,   5, 154,   7,
        18, 128, 226, 235,  39, 178, 117,   9, 131,  44,  26,  27, 110,  90, 160,  82,  59, 214, 179,  41,
        227,  47, 132,  83, 209,   0, 237,  32, 252, 177,  91, 106, 203, 190,  57,  74,  76,  88, 207, 208,
        239, 170, 251,  67,  77,  51, 133,  69, 249,   2, 127,  80,  60, 159, 168,  81, 163,  64, 143, 146,
        157,  56, 245, 188, 182, 218,  33,  16, 255, 243, 210, 205,  12,  19, 236,  95, 151,  68,  23, 196,
        167, 126,  61, 100,  93,  25, 115,  96, 129,  79, 220,  34,  42, 144, 136,  70, 238, 184,  20, 222,
        94,  11, 219, 224,  50,  58,  10,  73,   6,  36,  92, 194, 211, 172,  98, 145, 149, 228, 121, 231,
        200,  55, 109, 141, 213,  78, 169, 108,  86, 244, 234, 101, 122, 174,   8, 186, 120,  37,  46,  28,
        166, 180, 198, 232, 221, 116,  31,  75, 189, 139, 138, 112,  62, 181, 102,  72,   3, 246,  14,  97,
        53,  87, 185, 134, 193,  29, 158, 225, 248, 152,  17, 105, 217, 142, 148, 155,  30, 135, 233, 206,
        85,  40, 223, 140, 161, 137,  13, 191, 230,  66, 104,  65, 153,  45,  15, 176,  84, 187,  22}
    local inv_s_box	= { 82,   9, 106, 213,  48,  54, 165,  56, 191,  64, 163, 158, 129, 243, 215, 251, 124,
        227,  57, 130, 155,  47, 255, 135,  52, 142,  67,  68, 196, 222, 233, 203,  84, 123, 148,  50, 166,
        194,  35,  61, 238,  76, 149,  11,  66, 250, 195,  78,   8,  46, 161, 102,  40, 217,  36, 178, 118,
        91, 162,  73, 109, 139, 209,  37, 114, 248, 246, 100, 134, 104, 152,  22, 212, 164,  92, 204,  93,
        101, 182, 146, 108, 112,  72,  80, 253, 237, 185, 218,  94,  21,  70,  87, 167, 141, 157, 132, 144,
        216, 171,   0, 140, 188, 211,  10, 247, 228,  88,   5, 184, 179,  69,   6, 208,  44,  30, 143, 202,
        63,  15,   2, 193, 175, 189,   3,   1,  19, 138, 107,  58, 145,  17,  65,  79, 103, 220, 234, 151,
        242, 207, 206, 240, 180, 230, 115, 150, 172, 116,  34, 231, 173,  53, 133, 226, 249,  55, 232,  28,
        117, 223, 110,  71, 241,  26, 113,  29,  41, 197, 137, 111, 183,  98,  14, 170,  24, 190,  27, 252,
        86,  62,  75, 198, 210, 121,  32, 154, 219, 192, 254, 120, 205,  90, 244,  31, 221, 168,  51, 136,
        7, 199,  49, 177,  18,  16,  89,  39, 128, 236,  95,  96,  81, 127, 169,  25, 181,  74,  13,  45,
        229, 122, 159, 147, 201, 156, 239, 160, 224,  59,  77, 174,  42, 245, 176, 200, 235, 187,  60, 131,
        83, 153,  97,  23,  43,   4, 126, 186, 119, 214,  38, 225, 105,  20,  99,  85,  33,  12, 125}

    -- ROUND CONSTANTS ARRAY
    local rcon = {  0,   1,   2,   4,   8,  16,  32,  64, 128,  27,  54, 108, 216, 171,  77, 154,  47,  94,
        188,  99, 198, 151,  53, 106, 212, 179, 125, 250, 239, 197, 145,  57}
    -- MULTIPLICATION OF BINARY POLYNOMIAL
    local function xtime(x)
        local i = lshift(x, 1)
        return if band(x, 128) == 0 then i else bxor(i, 27) % 256
    end

    -- TRANSFORMATION FUNCTIONS
    local function subBytes		(s, inv) 		-- Processes State using the S-box
        inv = if inv then inv_s_box else s_box
        for i = 1, 4 do
            for j = 1, 4 do
                s[i][j] = inv[s[i][j] + 1]
            end
        end
    end
    local function shiftRows		(s, inv) 	-- Processes State by circularly shifting rows
        s[1][3], s[2][3], s[3][3], s[4][3] = s[3][3], s[4][3], s[1][3], s[2][3]
        if inv then
            s[1][2], s[2][2], s[3][2], s[4][2] = s[4][2], s[1][2], s[2][2], s[3][2]
            s[1][4], s[2][4], s[3][4], s[4][4] = s[2][4], s[3][4], s[4][4], s[1][4]
        else
            s[1][2], s[2][2], s[3][2], s[4][2] = s[2][2], s[3][2], s[4][2], s[1][2]
            s[1][4], s[2][4], s[3][4], s[4][4] = s[4][4], s[1][4], s[2][4], s[3][4]
        end
    end
    local function addRoundKey	(s, k) 			-- Processes Cipher by adding a round key to the State
        for i = 1, 4 do
            for j = 1, 4 do
                s[i][j] = bxor(s[i][j], k[i][j])
            end
        end
    end
    local function mixColumns	(s, inv) 		-- Processes Cipher by taking and mixing State columns
        local t, u
        if inv then
            for i = 1, 4 do
                t = xtime(xtime(bxor(s[i][1], s[i][3])))
                u = xtime(xtime(bxor(s[i][2], s[i][4])))
                s[i][1], s[i][2] = bxor(s[i][1], t), bxor(s[i][2], u)
                s[i][3], s[i][4] = bxor(s[i][3], t), bxor(s[i][4], u)
            end
        end

        local i
        for j = 1, 4 do
            i = s[j]
            t, u = bxor		(i[1], i[2], i[3], i[4]), i[1]
            for k = 1, 4 do
                i[k] = bxor	(i[k], t, xtime(bxor(i[k], i[k + 1] or u)))
            end
        end
    end

    -- BYTE ARRAY UTILITIES
    local function bytesToMatrix	(t, c, inv) -- Converts a byte array to a 4x4 matrix
        if inv then
            table.move		(c[1], 1, 4, 1, t)
            table.move		(c[2], 1, 4, 5, t)
            table.move		(c[3], 1, 4, 9, t)
            table.move		(c[4], 1, 4, 13, t)
        else
            for i = 1, #c / 4 do
                table.clear	(t[i])
                table.move	(c, i * 4 - 3, i * 4, 1, t[i])
            end
        end

        return t
    end
    local function xorBytes		(t, a, b) 		-- Returns bitwise bxor of all their bytes
        table.clear		(t)

        for i = 1, math.min(#a, #b) do
            table.insert(t, bxor(a[i], b[i]))
        end
        return t
    end
    local function incBytes		(a, inv)		-- Increment byte array by one
        local o = true
        for i = if inv then 1 else #a, if inv then #a else 1, if inv then 1 else - 1 do
            if a[i] == 255 then
                a[i] = 0
            else
                a[i] += 1
                o = false
                break
            end
        end

        return o, a
    end

    -- MAIN ALGORITHM
    local function expandKey	(key) 				-- Key expansion
        local kc = bytesToMatrix(if #key == 16 then {{}, {}, {}, {}} elseif #key == 24 then {{}, {}, {}, {}
            , {}, {}} else {{}, {}, {}, {}, {}, {}, {}, {}}, key)
        local is = #key / 4
        local i, t, w = 2, {}, nil

        while #kc < (#key / 4 + 7) * 4 do
            w = table.clone	(kc[#kc])
            if #kc % is == 0 then
                table.insert(w, table.remove(w, 1))
                for j = 1, 4 do
                    w[j] = s_box[w[j] + 1]
                end
                w[1]	 = bxor(w[1], rcon[i])
                i 	+= 1
            elseif #key == 32 and #kc % is == 4 then
                for j = 1, 4 do
                    w[j] = s_box[w[j] + 1]
                end
            end

            table.clear	(t)
            xorBytes	(w, table.move(w, 1, 4, 1, t), kc[#kc - is + 1])
            table.insert(kc, w)
        end

        table.clear		(t)
        for i = 1, #kc / 4 do
            table.insert(t, {})
            table.move	(kc, i * 4 - 3, i * 4, 1, t[#t])
        end
        return t
    end
    local function encrypt	(key, km, pt, ps, r) 	-- Block cipher encryption
        bytesToMatrix	(ps, pt)
        addRoundKey		(ps, km[1])

        for i = 2, #key / 4 + 6 do
            subBytes	(ps)
            shiftRows	(ps)
            mixColumns	(ps)
            addRoundKey	(ps, km[i])
        end
        subBytes		(ps)
        shiftRows		(ps)
        addRoundKey		(ps, km[#km])

        return bytesToMatrix(r, ps, true)
    end
    local function decrypt	(key, km, ct, cs, r) 	-- Block cipher decryption
        bytesToMatrix	(cs, ct)

        addRoundKey		(cs, km[#km])
        shiftRows		(cs, true)
        subBytes		(cs, true)
        for i = #key / 4 + 6, 2, - 1 do
            addRoundKey	(cs, km[i])
            mixColumns	(cs, true)
            shiftRows	(cs, true)
            subBytes	(cs, true)
        end

        addRoundKey		(cs, km[1])
        return bytesToMatrix(r, cs, true)
    end

    -- INITIALIZATION FUNCTIONS
    local function convertType	(a) 					-- Converts data to bytes if possible
        if type(a) == "string" then
            local r = {}

            for i = 1, string.len(a), 7997 do
                table.move({string.byte(a, i, i + 7996)}, 1, 7997, i, r)
            end
            return r
        elseif type(a) == "table" then
            for _, i in ipairs(a) do
                assert(type(i) == "number" and math.floor(i) == i and 0 <= i and i < 256,
                    "Unable to cast value to bytes")
            end
            return a
        else
            error("Unable to cast value to bytes")
        end
    end
    local function init			(key, txt, m, iv, s) 	-- Initializes functions if possible
        key = convertType(key)
        assert(#key == 16 or #key == 24 or #key == 32, "Key must be either 16, 24 or 32 bytes long")
        txt = convertType(txt)
        assert(#txt % (s or 16) == 0, "Input must be a multiple of " .. (if s then "segment size " .. s
            else "16") .. " bytes in length")
        if m then
            if type(iv) == "table" then
                iv = table.clone(iv)
                local l, e 		= iv.Length, iv.LittleEndian
                assert(type(l) == "number" and 0 < l and l <= 16,
                    "Counter value length must be between 1 and 16 bytes")
                iv.Prefix 		= convertType(iv.Prefix or {})
                iv.Suffix 		= convertType(iv.Suffix or {})
                assert(#iv.Prefix + #iv.Suffix + l == 16, "Counter must be 16 bytes long")
                iv.InitValue 	= if iv.InitValue == nil then {1} else table.clone(convertType(iv.InitValue
                ))
                assert(#iv.InitValue <= l, "Initial value length must be of the counter value")
                iv.InitOverflow = if iv.InitOverflow == nil then table.create(l, 0) else table.clone(convertType(iv.InitOverflow))
                assert(#iv.InitOverflow <= l,
                    "Initial overflow value length must be of the counter value")
                for _ = 1, l - #iv.InitValue do
                    table.insert(iv.InitValue, 1 + if e then #iv.InitValue else 0, 0)
                end
                for _ = 1, l - #iv.InitOverflow do
                    table.insert(iv.InitOverflow, 1 + if e then #iv.InitOverflow else 0, 0)
                end
            elseif type(iv) ~= "function" then
                local i, t = if iv then convertType(iv) else table.create(16, 0), {}
                assert(#i == 16, "Counter must be 16 bytes long")
                iv = {Length = 16, Prefix = t, Suffix = t, InitValue = i,
                    InitOverflow = table.create(16, 0)}
            end
        elseif m == false then
            iv 	= if iv == nil then  table.create(16, 0) else convertType(iv)
            assert(#iv == 16, "Initialization vector must be 16 bytes long")
        end
        if s then
            s = math.floor(tonumber(s) or 1)
            assert(type(s) == "number" and 0 < s and s <= 16, "Segment size must be between 1 and 16 bytes"
            )
        end

        return key, txt, expandKey(key), iv, s
    end
    type bytes = {number} -- Type instance of a valid bytes object

    -- CIPHER MODES OF OPERATION
    return {
        -- Electronic codebook (ECB)
        encrypt_ECB = function(key : bytes, plainText : bytes) 									: bytes
            local km
            key, plainText, km = init(key, plainText)

            local b, k, s, t = {}, {}, {{}, {}, {}, {}}, {}
            for i = 1, #plainText, 16 do
                table.move(plainText, i, i + 15, 1, k)
                table.move(encrypt(key, km, k, s, t), 1, 16, i, b)
            end

            return b
        end,
        decrypt_ECB = function(key : bytes, cipherText : bytes) 								: bytes
            local km
            key, cipherText, km = init(key, cipherText)

            local b, k, s, t = {}, {}, {{}, {}, {}, {}}, {}
            for i = 1, #cipherText, 16 do
                table.move(cipherText, i, i + 15, 1, k)
                table.move(decrypt(key, km, k, s, t), 1, 16, i, b)
            end

            return b
        end,
        -- Cipher block chaining (CBC)
        encrypt_CBC = function(key : bytes, plainText : bytes, initVector : bytes?) 			: bytes
            local km
            key, plainText, km, initVector = init(key, plainText, false, initVector)

            local b, k, p, s, t = {}, {}, initVector, {{}, {}, {}, {}}, {}
            for i = 1, #plainText, 16 do
                table.move(plainText, i, i + 15, 1, k)
                table.move(encrypt(key, km, xorBytes(t, k, p), s, p), 1, 16, i, b)
            end

            return b
        end,
        decrypt_CBC = function(key : bytes, cipherText : bytes, initVector : bytes?) 			: bytes
            local km
            key, cipherText, km, initVector = init(key, cipherText, false, initVector)

            local b, k, p, s, t = {}, {}, initVector, {{}, {}, {}, {}}, {}
            for i = 1, #cipherText, 16 do
                table.move(cipherText, i, i + 15, 1, k)
                table.move(xorBytes(k, decrypt(key, km, k, s, t), p), 1, 16, i, b)
                table.move(cipherText, i, i + 15, 1, p)
            end

            return b
        end,
        -- Propagating cipher block chaining (PCBC)
        encrypt_PCBC = function(key : bytes, plainText : bytes, initVector : bytes?) 			: bytes
            local km
            key, plainText, km, initVector = init(key, plainText, false, initVector)

            local b, k, c, p, s, t = {}, {}, initVector, table.create(16, 0), {{}, {}, {}, {}}, {}
            for i = 1, #plainText, 16 do
                table.move(plainText, i, i + 15, 1, k)
                table.move(encrypt(key, km, xorBytes(k, xorBytes(t, c, k), p), s, c), 1, 16, i, b)
                table.move(plainText, i, i + 15, 1, p)
            end

            return b
        end,
        decrypt_PCBC = function(key : bytes, cipherText : bytes, initVector : bytes?) 			: bytes
            local km
            key, cipherText, km, initVector = init(key, cipherText, false, initVector)

            local b, k, c, p, s, t = {}, {}, initVector, table.create(16, 0), {{}, {}, {}, {}}, {}
            for i = 1, #cipherText, 16 do
                table.move(cipherText, i, i + 15, 1, k)
                table.move(xorBytes(p, decrypt(key, km, k, s, t), xorBytes(k, c, p)), 1, 16, i, b)
                table.move(cipherText, i, i + 15, 1, c)
            end

            return b
        end,
        -- Cipher feedback (CFB)
        encrypt_CFB = function(key : bytes, plainText : bytes, initVector : bytes?, segmentSize : number?)
            : bytes
            local km
            key, plainText, km, initVector, segmentSize = init(key, plainText, false, initVector,
                if segmentSize == nil then 1 else segmentSize)

            local b, k, p, q, s, t = {}, {}, initVector, {}, {{}, {}, {}, {}}, {}
            for i = 1, #plainText, segmentSize do
                table.move(plainText, i, i + segmentSize - 1, 1, k)
                table.move(xorBytes(q, encrypt(key, km, p, s, t), k), 1, segmentSize, i, b)
                for j = 16, segmentSize + 1, - 1 do
                    table.insert(q, 1, p[j])
                end
                table.move(q, 1, 16, 1, p)
            end

            return b
        end,
        decrypt_CFB = function(key : bytes, cipherText : bytes, initVector : bytes, segmentSize : number?)
            : bytes
            local km
            key, cipherText, km, initVector, segmentSize = init(key, cipherText, false, initVector,
                if segmentSize == nil then 1 else segmentSize)

            local b, k, p, q, s, t = {}, {}, initVector, {}, {{}, {}, {}, {}}, {}
            for i = 1, #cipherText, segmentSize do
                table.move(cipherText, i, i + segmentSize - 1, 1, k)
                table.move(xorBytes(q, encrypt(key, km, p, s, t), k), 1, segmentSize, i, b)
                for j = 16, segmentSize + 1, - 1 do
                    table.insert(k, 1, p[j])
                end
                table.move(k, 1, 16, 1, p)
            end

            return b
        end,
        -- Output feedback (OFB)
        encrypt_OFB = function(key : bytes, plainText : bytes, initVector : bytes?) 			: bytes
            local km
            key, plainText, km, initVector = init(key, plainText, false, initVector)

            local b, k, p, s, t = {}, {}, initVector, {{}, {}, {}, {}}, {}
            for i = 1, #plainText, 16 do
                table.move(plainText, i, i + 15, 1, k)
                table.move(encrypt(key, km, p, s, t), 1, 16, 1, p)
                table.move(xorBytes(t, k, p), 1, 16, i, b)
            end

            return b
        end,
        -- Counter (CTR)
        encrypt_CTR = function(key : bytes, plainText : bytes, counter : ((bytes) -> bytes) | bytes | { [
            string]: any }?) : bytes
            local km
            key, plainText, km, counter = init(key, plainText, true, counter)

            local b, k, c, s, t, r, n = {}, {}, {}, {{}, {}, {}, {}}, {}, type(counter) == "table", nil
            for i = 1, #plainText, 16 do
                if r then
                    if i > 1 and incBytes(counter.InitValue, counter.LittleEndian) then
                        table.move(counter.InitOverflow, 1, 16, 1, counter.InitValue)
                    end
                    table.clear	(c)
                    table.move	(counter.Prefix, 1, #counter.Prefix, 1, c)
                    table.move	(counter.InitValue, 1, counter.Length, #c + 1, c)
                    table.move	(counter.Suffix, 1, #counter.Suffix, #c + 1, c)
                else
                    n = convertType(counter(c, (i + 15) / 16))
                    assert		(#n == 16, "Counter must be 16 bytes long")
                    table.move	(n, 1, 16, 1, c)
                end
                table.move(plainText, i, i + 15, 1, k)
                table.move(xorBytes(c, encrypt(key, km, c, s, t), k), 1, 16, i, b)
            end

            return b
        end
    } -- Returns the library
end


function RoCrypt.hmac(hash_func, key, message, AsBinary)
    local function HexToBinFunction(hh)
        return string.char(tonumber(hh, 16))
    end

    local function hex2bin(hex_string)
        return (string.gsub(hex_string, "%x%x", HexToBinFunction))
    end

    local BinaryStringMap = {}
    for Index = 0, 255 do
        BinaryStringMap[string.format("%02x", Index)] = string.char(Index)
    end

    local block_size_for_HMAC = {
        [RoCrypt.md5] = 64;
        [RoCrypt.sha224] = 64;
        [RoCrypt.sha256] = 64;
        [RoCrypt.sha384] = 128;
        [RoCrypt.sha512] = 128;
    }
    -- Create an instance (private objects for current calculation)
    local block_size = block_size_for_HMAC[hash_func]
    if not block_size then
        error("Unknown hash function", 2)
    end

    local KeyLength = #key
    if KeyLength > block_size then
        key = string.gsub(hash_func(key), "%x%x", HexToBinFunction)
        KeyLength = #key
    end

    local append = hash_func()(string.gsub(key, ".", function(c)
        return string.char(bxor(string.byte(c), 0x36))
    end) .. string.rep("6", block_size - KeyLength)) -- 6 = string.char(0x36)

    local result

    local function partial(message_part)
        if not message_part then
            result = result or hash_func(
                string.gsub(key, ".", function(c)
                    return string.char(bxor(string.byte(c), 0x5c))
                end) .. string.rep("\\", block_size - KeyLength) -- \ = string.char(0x5c)
                    .. (string.gsub(append(), "%x%x", HexToBinFunction))
            )

            return result
        elseif result then
            error("Adding more chunks is not allowed after receiving the result", 2)
        else
            append(message_part)
            return partial
        end
    end

    if message then
        -- Actually perform calculations and return the HMAC of a message
        local FinalMessage = partial(message)()
        return AsBinary and (string.gsub(FinalMessage, "%x%x", BinaryStringMap)) or FinalMessage
    else
        -- Return function for chunk-by-chunk loading of a message
        -- User should feed every chunk of the message as single argument to this function and finally get HMAC by invoking this function without an argument
        return partial
    end
end




return RoCrypt
