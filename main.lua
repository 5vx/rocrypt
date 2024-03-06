--[[
RoCrypt
----------------------------------------------------------------------------------------
DESCRIPTION:
	This module contains functions to calculate SHA digest:
	    SHA-256, SHA-512
	Written in pure Lua.
USAGE:
	Input data should be a string
	Result (SHA digest) is returned in hexadecimal representation as a string of lowercase hex digits.
	Simplest usage example:
		local RoCrypt = require(script.RoCrypt)
		local hash = RoCrypt.sha256("string here")
	SHA2 hash functions:
		HashLib.sha256
		HashLib.sha512
--]]--

RoCrypt = {}
band, bxor, bnot, rrotate, rshift = bit32.band, bit32.bxor, bit32.bnot, bit32.rrotate, bit32.rshift


function RoCrypt.sha256(message)
    
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


function RoCrypt.sha512(message)
    
end

return RoCrypt
