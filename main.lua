--[[
RoCrypt
----------------------------------------------------------------------------------------
DESCRIPTION:
    TODO: GZIP (?), Blowfish, Bcrypt, Argon2, (?) BLAKE3, BLAKE2S, BLAKE2B, DES, DES3
	This module contains cryptographic hash functions (CHF)
	   MD2, MD4, MD5 
	   RIPEMD-128, RIPEMD-160
	   SHA1, SHA-224, SHA-256, SHA-384, SHA-512, SHA3-224, SHA3-256, SHA3-384, SHA3-512
	   SHAKE128, SHAKE256
	Cyclic redundancy checks (CRC) algorithms
        CRC32
    Binary-to-hex/encoding algorithms
        Base64
        Base91
    Asymmetric algorithms
        RSA
    Symmetric block cipher algorithms
        AES
        DES, Triple DES
    Shared-secret algorithms
        HMAC
    Compression algorithms
        LZ4, ZLIB, Deflate
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
	    RoCrypt.sha1()
		RoCrypt.sha224()
		RoCrypt.sha256()
		RoCrypt.sha384()
		RoCrypt.sha512()
		RoCrypt.sha3_224()
		RoCrypt.sha3_256()
		RoCrypt.sha3_384()
		RoCrypt.sha3_512()
		RoCrypt.shake128()
		RoCrypt.shake256()
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
CREDIT: RobloxGamerPro200007
Egor-Skriptunoff
github.com/somesocks/lua-lockbox

--]]--



RoCrypt = {
    utils = {
    },
    compression = {

    }
}

--[[--
    cache aliases
    still has a pretty nice optimization despite it technically being unneeded in the newer luau VMs
    looks messy, but the next best alternative would be setfenv, which isn't exactly a good solution (is deprecated and disables certain luau VM optimizations)
]]--

local ipairs = ipairs
local band, bxor, bnot, rrotate, rshift, bor, lrotate, lshift, extract = bit32.band, bit32.bxor, bit32.bnot, bit32.rrotate, bit32.rshift, bit32.bor, bit32.lrotate, bit32.lshift, bit32.extract
local char, rep, sub, format, byte, sfind, len, reverse, gmatch = string.char, string.rep, string.sub, string.format, string.byte, string.find, string.len, string.reverse, string.gmatch
local floor = math.floor
local tfind, clear, move = table.find, table.clear, table.move
local bit, E = bit32, nil

local persistent = {
    snowflake = {
        id = nil,
        increment = 0,
        last = 0,
    },
    md5 = {
        common_W = {}
    },
    pi = (function(digits, includeDecimal)
        return string.sub("1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679821480865132823066470938446095505822317253594081284811174502841027019385211055596446229489549303819644288109756659334461284756482337867831652712019091456485669234603486104543266482133936072602491412737245870066063155881748815209209628292540917153643678925903600113305305488204665213841469519415116094330572703657595919530921861173819326117931051185480744623799627495673518857527248912279381830119491298336733624406566430860213949463952247371907021798609437027705392171762931767523846748184676694051320005681271452635608277857713427577896091736371787214684409012249534301465495853710507922796892589235420199561121290219608640344181598136297747713099605187072113499999983729780499510597317328160963185950244594553469083026425223082533446850352619311881710100031378387528865875332083814206171776691473035982534904287554687311595628638823537875937519577818577805321712268066130019278766111959092164201989", 1, digits)
    end)
}




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
function RoCrypt.utils.array()
    local Array = {};

    Array.size = function(array)
        return #array;
    end

    Array.fromString = function(string)
        local bytes = {};

        local i = 1;
        local byte = string.byte(string, i);
        while byte ~= nil do
            bytes[i] = byte;
            i = i + 1;
            byte = string.byte(string, i);
        end

        return bytes;

    end

    Array.toString = function(bytes)
        local chars = {};
        local i = 1;

        local byte = bytes[i];
        while byte ~= nil do
            chars[i] = string.char(byte);
            i = i + 1;
            byte = bytes[i];
        end

        return table.concat(chars, "");
    end

    Array.fromStream = function(stream)
        local array = {};
        local i = 1;

        local byte = stream();
        while byte ~= nil do
            array[i] = byte;
            i = i + 1;
            byte = stream();
        end

        return array;
    end

    Array.readFromQueue = function(queue, size)
        local array = {};

        for i = 1, size do
            array[i] = queue.pop();
        end

        return array;
    end

    Array.writeToQueue = function(queue, array)
        local size = Array.size(array);

        for i = 1, size do
            queue.push(array[i]);
        end
    end

    Array.toStream = function(array)
        local queue = RoCrypt.utils.queue();
        local i = 1;

        local byte = array[i];
        while byte ~= nil do
            queue.push(byte);
            i = i + 1;
            byte = array[i];
        end

        return queue.pop;
    end


    local fromHexTable = {};
    for i = 0, 255 do
        fromHexTable[string.format("%02X", i)] = i;
        fromHexTable[string.format("%02x", i)] = i;
    end

    Array.fromHex = function(hex)
        local array = {};

        for i = 1, string.len(hex) / 2 do
            local h = string.sub(hex, i * 2 - 1, i * 2);
            array[i] = fromHexTable[h];
        end

        return array;
    end


    local toHexTable = {};
    for i = 0, 255 do
        toHexTable[i] = string.format("%02X", i);
    end

    Array.toHex = function(array)
        local hex = {};
        local i = 1;

        local byte = array[i];
        while byte ~= nil do
            hex[i] = toHexTable[byte];
            i = i + 1;
            byte = array[i];
        end

        return table.concat(hex, "");

    end

    Array.concat = function(a, b)
        local concat = {};
        local out = 1;

        local i = 1;
        local byte = a[i];
        while byte ~= nil do
            concat[out] = byte;
            i = i + 1;
            out = out + 1;
            byte = a[i];
        end

        i = 1;
        byte = b[i];
        while byte ~= nil do
            concat[out] = byte;
            i = i + 1;
            out = out + 1;
            byte = b[i];
        end

        return concat;
    end

    Array.truncate = function(a, newSize)
        local x = {};

        for i = 1, newSize do
            x[i] = a[i];
        end

        return x;
    end

    Array.bxor = function(a, b)
        local x = {};

        for k, v in pairs(a) do
            x[k] = bxor(v, b[k]);
        end

        return x;
    end

    Array.substitute = function(input, sbox)
        local out = {};

        for k, v in pairs(input) do
            out[k] = sbox[v];
        end

        return out;
    end

    Array.permute = function(input, pbox)
        local out = {};

        for k, v in pairs(pbox) do
            out[k] = input[v];
        end

        return out;
    end

    Array.copy = function(input)
        local out = {};

        for k, v in pairs(input) do
            out[k] = v;
        end
        return out;
    end

    Array.slice = function(input, start, stop)
        local out = {};

        if start == nil then
            start = 1
        elseif start < 0 then
            start = #input + start + 1
        end
        if stop == nil then
            stop = #input
        elseif stop < 0 then
            stop = #input + stop + 1
        end

        for i = start, stop do
            table.insert(out, input[i])
        end

        return out;
    end

    return Array;
end

function RoCrypt.utils.stream()
    local Queue = RoCrypt.utils.queue()
    local String = string

    local Stream = {};


    Stream.fromString = function(string)
        local i = 0;
        return function()
            i = i + 1;
            return String.byte(string, i);
        end
    end


    Stream.toString = function(stream)
        local array = {};
        local i = 1;

        local byte = stream();
        while byte ~= nil do
            array[i] = String.char(byte);
            i = i + 1;
            byte = stream();
        end

        return table.concat(array);
    end


    Stream.fromArray = function(array)
        local queue = Queue();
        local i = 1;

        local byte = array[i];
        while byte ~= nil do
            queue.push(byte);
            i = i + 1;
            byte = array[i];
        end

        return queue.pop;
    end


    Stream.toArray = function(stream)
        local array = {};
        local i = 1;

        local byte = stream();
        while byte ~= nil do
            array[i] = byte;
            i = i + 1;
            byte = stream();
        end

        return array;
    end


    local fromHexTable = {};
    for i = 0, 255 do
        fromHexTable[String.format("%02X", i)] = i;
        fromHexTable[String.format("%02x", i)] = i;
    end

    Stream.fromHex = function(hex)
        local queue = Queue();

        for i = 1, String.len(hex) / 2 do
            local h = String.sub(hex, i * 2 - 1, i * 2);
            queue.push(fromHexTable[h]);
        end

        return queue.pop;
    end



    local toHexTable = {};
    for i = 0, 255 do
        toHexTable[i] = String.format("%02X", i);
    end

    Stream.toHex = function(stream)
        local hex = {};
        local i = 1;

        local byte = stream();
        while byte ~= nil do
            hex[i] = toHexTable[byte];
            i = i + 1;
            byte = stream();
        end

        return table.concat(hex);
    end

    return Stream;
end



function RoCrypt.utils.queue_buffer()
    local Queue = function()
        local queue = buffer.create(4096)
        local tail = 0
        local head = 0

        local public = {}

        public.push = function(obj)
            buffer.writeu8(queue, head, obj)
            head = head + 1
            if head >= buffer.len(queue) then
                local newQueue = buffer.create(buffer.len(queue) * 2)
                buffer.copy(newQueue, 0, queue, 0, buffer.len(queue))
                queue = newQueue
            end
        end

        public.pop = function()
            if tail < head then
                local obj = buffer.readu8(queue, tail)
                tail = tail + 1
                return obj
            else
                return nil
            end
        end

        public.size = function()
            return head - tail
        end

        public.getHead = function()
            return head
        end

        public.getTail = function()
            return tail
        end

        public.reset = function()
            queue = buffer.create(4096)
            head = 0
            tail = 0
        end

        return public
    end

    return Queue()
end

function RoCrypt.utils.array_buffer()
    local Array = {}

    Array.size = function(array)
        return buffer.len(array)
    end

    Array.fromString = function(string)
        return buffer.fromstring(string)
    end

    Array.toString = function(bytes)
        return buffer.tostring(bytes)
    end

    Array.fromStream = function(stream)
        local array = buffer.create(4096)
        local i = 0

        local byte = stream()
        while byte ~= nil do
            buffer.writeu8(array, i, byte)
            i = i + 1
            if i >= buffer.len(array) then
                local newArray = buffer.create(buffer.len(array) * 2)
                buffer.copy(newArray, 0, array, 0, buffer.len(array))
                array = newArray
            end
            byte = stream()
        end

        local result = buffer.create(i)
        buffer.copy(result, 0, array, 0, i)
        return result
    end

    Array.readFromQueue = function(queue, size)
        local array = buffer.create(size)

        for i = 0, size - 1 do
            buffer.writeu8(array, i, queue.pop())
        end

        return array
    end

    Array.writeToQueue = function(queue, array)
        local size = buffer.len(array)

        for i = 0, size - 1 do
            queue.push(buffer.readu8(array, i))
        end
    end

    Array.toStream = function(array)
        local queue = RoCrypt.utils.queue()
        local i = 0

        return function()
            if i < buffer.len(array) then
                local byte = buffer.readu8(array, i)
                i = i + 1
                return byte
            else
                return nil
            end
        end
    end

    local fromHexTable = buffer.create(256)
    for i = 0, 255 do
        local hex = string.format("%02X", i)
        buffer.writeu8(fromHexTable, string.byte(hex, 1), i)
        buffer.writeu8(fromHexTable, string.byte(hex, 2), i)
    end

    Array.fromHex = function(hex)
        local array = buffer.create(string.len(hex) / 2)

        for i = 0, buffer.len(array) - 1 do
            local h1 = string.byte(hex, i * 2 + 1)
            local h2 = string.byte(hex, i * 2 + 2)
            buffer.writeu8(array, i, bor(lshift(buffer.readu8(fromHexTable, h1), 4), buffer.readu8(fromHexTable, h2)))
        end

        return array
    end

    local toHexTable = buffer.create(256)
    for i = 0, 255 do
        local hex = string.format("%02X", i)
        buffer.writestring(toHexTable, i * 2, hex)
    end

    Array.toHex = function(array)
        local hex = buffer.create(buffer.len(array) * 2)

        for i = 0, buffer.len(array) - 1 do
            local byte = buffer.readu8(array, i)
            buffer.writestring(hex, i * 2, buffer.readstring(toHexTable, byte * 2, 2))
        end

        return buffer.tostring(hex)
    end

    Array.concat = function(a, b)
        local result = buffer.create(buffer.len(a) + buffer.len(b))
        buffer.copy(result, 0, a, 0, buffer.len(a))
        buffer.copy(result, buffer.len(a), b, 0, buffer.len(b))
        return result
    end

    Array.truncate = function(a, newSize)
        local result = buffer.create(newSize)
        buffer.copy(result, 0, a, 0, newSize)
        return result
    end

    Array.bxor = function(a, b)
        local x = buffer.create(buffer.len(a))

        for i = 0, buffer.len(a) - 1 do
            buffer.writeu8(x, i, bxor(buffer.readu8(a, i), buffer.readu8(b, i)))
        end

        return x
    end

    Array.substitute = function(input, sbox)
        local out = buffer.create(buffer.len(input))

        for i = 0, buffer.len(input) - 1 do
            buffer.writeu8(out, i, buffer.readu8(sbox, buffer.readu8(input, i)))
        end

        return out
    end

    Array.permute = function(input, pbox)
        local out = buffer.create(buffer.len(input))

        for i = 0, buffer.len(pbox) - 1 do
            buffer.writeu8(out, i, buffer.readu8(input, buffer.readu8(pbox, i) - 1))
        end

        return out
    end

    Array.copy = function(input)
        local result = buffer.create(buffer.len(input))
        buffer.copy(result, 0, input, 0, buffer.len(input))
        return result
    end

    Array.slice = function(input, start, stop)
        if start == nil then
            start = 0
        elseif start < 0 then
            start = buffer.len(input) + start
        end
        if stop == nil then
            stop = buffer.len(input)
        elseif stop < 0 then
            stop = buffer.len(input) + stop
        end

        local result = buffer.create(stop - start)
        buffer.copy(result, 0, input, start, stop - start)
        return result
    end

    return Array
end



function RoCrypt.utils.isStringHex(str)
    if type(str) == "string" then
        local hexPattern = '^%x+$'
        return string.match(str, hexPattern) ~= nil
    else 
        return false
    end
end

function RoCrypt.utils.bytes2word(b0,b1,b2,b3)
    local i = b3; i = lshift(i, 8)
    i = bor(i, b2); i = lshift(i, 8)
    i = bor(i, b1); i = lshift(i, 8)
    i = bor(i, b0)
    return i
end

function RoCrypt.utils.hex2bytes(hex)
    local bytes = {}
    for i = 1, #hex, 2 do
        local byte = tonumber(hex:sub(i, i+1), 16)
        table.insert(bytes, byte)
    end
    return bytes
end
function RoCrypt.utils.hex2string(hex)
    local bytes = {}
    for i = 1, #hex, 2 do
        local byte = tonumber(hex:sub(i, i+1), 16)
        table.insert(bytes, byte)
    end

    local str = ""
    for i = 1, #bytes do
        str = str .. string.char(bytes[i])
    end
    return str
end

function RoCrypt.utils.table2size(t)
    local size = 0

    for _, v in pairs(t) do
        if type(v) == "string" then
            size = size + #v
        elseif type(v) == "number" then
            size = size + 8
        elseif type(v) == "boolean" then
            size = size + 1
        elseif type(v) == "table" then
            size = size + RoCrypt.utils.tablesize(v)
        else
            size = size + 4  -- Assuming other types (functions, userdata) take 4 bytes
        end
    end

    return size
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
    local b4, b5, b6, b7 = RoCrypt.utils.word2bytes(floor(i / 0x100000000))
    local b0, b1, b2, b3 = RoCrypt.utils.word2bytes(i)
    return b0, b1, b2, b3, b4, b5, b6, b7
end


function RoCrypt.utils.bytes2hex(byteArray)
    local hexString = ""
    for _, byte in ipairs(byteArray) do
        hexString = hexString .. string.format("%02x", byte)
    end
    return hexString

end

function RoCrypt.utils.string2hex(str)
    local hex = ""
    for i = 1, #str do
        local byte = string.byte(str, i)
        hex = hex .. string.format("%02x", byte)
    end
    return hex
end

function RoCrypt.utils.string2bytes(str)
    local byteArray = {}
    for i = 1, #str do
        local c = string.sub(str, i, i)
        table.insert(byteArray, string.byte(c))
    end

    return byteArray
end

function RoCrypt.utils.bytes2string(byteArray)
    local str = ""
    for i = 1, #byteArray do
        local byte = byteArray[i]
        str = str .. string.char(byte)
    end

    return str
end




function RoCrypt.utils.randomBytes(n, outputFormat)
    local function seedGenerator()
        local timeSeed = tick() * 1e7 
        local randSeed = Random.new().NextInteger(Random.new(), -2147483648, 2147483647)
        return timeSeed + randSeed
    end
    local complexSeed = seedGenerator()
    local randomGenerator = Random.new(complexSeed)

    local bytes = {}
    for i = 1, n do
        local randomByte = randomGenerator:NextInteger(0, 255)
        bytes[i] = randomByte
    end
    local shuffleGenerator = Random.new(seedGenerator()) 
    for i = n, 2, -1 do  -- Fisher-Yates shuffle
        local j = shuffleGenerator:NextInteger(1, i)
        bytes[i], bytes[j] = bytes[j], bytes[i]
    end

    if outputFormat == "string" then
        for i,v in pairs(bytes) do 
            bytes[i] = string.char(v)
        end
        return table.concat(bytes)
    elseif outputFormat == "hex" then
        return RoCrypt.utils.bytes2hex(bytes)
    else  -- Default to table
        local byteTable = {}
        for i = 1, #bytes do
            byteTable[i] = string.byte(bytes[i])
        end
        return byteTable
    end
end

function RoCrypt.utils.packInt(i: number)
    return string.char(
        bit32.extract(i, 24, 8),
        bit32.extract(i, 16, 8),
        bit32.extract(i, 8, 8),
        bit32.extract(i, 0, 8)
    )
end



local function sha_bootstrapper()
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
        return format("%08x", x % 4294967296)
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
        sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, "SHA-512/"..tonumber(width).."\128"..rep("\0", 115).."\88", common_W, 0, 128)
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
                    local final_blocks = {tail, "\128", rep("\0", (-9 - length) % 64 + 1)}
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
                    local final_blocks = {tail, "\128", rep("\0", (-17-length) % 128 + 9)}
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

function keccak(block_size_in_bytes, digest_size, is_SHAKE, message)
    local sha2_K_lo, sha2_K_hi, sha2_H_lo, sha2_H_hi, sha3_RC_lo, sha3_RC_hi = {}, {}, {}, {}, {}, {}
    local HEX64, bxor64A5, lanes_index_base = nil, nil, nil -- defined only for branches that internally use 64-bit integers: "INT64" and "FFI"
    local K_lo_modulo, hi_factor, hi_factor_keccak = 4294967296, 0, 0
    do
        local sh_reg = 29
        local function next_bit()
            local r = sh_reg % 2
            sh_reg = bxor((sh_reg - r) / 2, 142 * r)
            return r
        end

        for idx = 1, 24 do
            local lo, m = 0, nil
            for _ = 1, 6 do
                m = m and m * m * 2 or 1
                lo = lo + next_bit() * m
            end

            local hi = next_bit() * m
            sha3_RC_hi[idx], sha3_RC_lo[idx] = hi, lo + hi * hi_factor_keccak
        end
    end




    local function keccak_feed(lanes_lo, lanes_hi, str, offs, size, block_size_in_bytes)
        -- This is an example of a Lua function having 79 local variables :-)
        -- offs >= 0, size >= 0, size is multiple of block_size_in_bytes, block_size_in_bytes is positive multiple of 8
        local RC_lo, RC_hi = sha3_RC_lo, sha3_RC_hi
        local qwords_qty = block_size_in_bytes / 8
        for pos = offs, offs + size - 1, block_size_in_bytes do
            for j = 1, qwords_qty do
                local a, b, c, d = string.byte(str, pos + 1, pos + 4)
                lanes_lo[j] = bxor(lanes_lo[j], ((d * 256 + c) * 256 + b) * 256 + a)
                pos = pos + 8
                a, b, c, d = string.byte(str, pos - 3, pos)
                lanes_hi[j] = bxor(lanes_hi[j], ((d * 256 + c) * 256 + b) * 256 + a)
            end

            local L01_lo, L01_hi, L02_lo, L02_hi, L03_lo, L03_hi, L04_lo, L04_hi, L05_lo, L05_hi, L06_lo, L06_hi, L07_lo, L07_hi, L08_lo, L08_hi, L09_lo, L09_hi, L10_lo, L10_hi, L11_lo, L11_hi, L12_lo, L12_hi, L13_lo, L13_hi, L14_lo, L14_hi, L15_lo, L15_hi, L16_lo, L16_hi, L17_lo, L17_hi, L18_lo, L18_hi, L19_lo, L19_hi, L20_lo, L20_hi, L21_lo, L21_hi, L22_lo, L22_hi, L23_lo, L23_hi, L24_lo, L24_hi, L25_lo, L25_hi = lanes_lo[1], lanes_hi[1], lanes_lo[2], lanes_hi[2], lanes_lo[3], lanes_hi[3], lanes_lo[4], lanes_hi[4], lanes_lo[5], lanes_hi[5], lanes_lo[6], lanes_hi[6], lanes_lo[7], lanes_hi[7], lanes_lo[8], lanes_hi[8], lanes_lo[9], lanes_hi[9], lanes_lo[10], lanes_hi[10], lanes_lo[11], lanes_hi[11], lanes_lo[12], lanes_hi[12], lanes_lo[13], lanes_hi[13], lanes_lo[14], lanes_hi[14], lanes_lo[15], lanes_hi[15], lanes_lo[16], lanes_hi[16], lanes_lo[17], lanes_hi[17], lanes_lo[18], lanes_hi[18], lanes_lo[19], lanes_hi[19], lanes_lo[20], lanes_hi[20], lanes_lo[21], lanes_hi[21], lanes_lo[22], lanes_hi[22], lanes_lo[23], lanes_hi[23], lanes_lo[24], lanes_hi[24], lanes_lo[25], lanes_hi[25]

            for round_idx = 1, 24 do
                local C1_lo = bxor(L01_lo, L06_lo, L11_lo, L16_lo, L21_lo)
                local C1_hi = bxor(L01_hi, L06_hi, L11_hi, L16_hi, L21_hi)
                local C2_lo = bxor(L02_lo, L07_lo, L12_lo, L17_lo, L22_lo)
                local C2_hi = bxor(L02_hi, L07_hi, L12_hi, L17_hi, L22_hi)
                local C3_lo = bxor(L03_lo, L08_lo, L13_lo, L18_lo, L23_lo)
                local C3_hi = bxor(L03_hi, L08_hi, L13_hi, L18_hi, L23_hi)
                local C4_lo = bxor(L04_lo, L09_lo, L14_lo, L19_lo, L24_lo)
                local C4_hi = bxor(L04_hi, L09_hi, L14_hi, L19_hi, L24_hi)
                local C5_lo = bxor(L05_lo, L10_lo, L15_lo, L20_lo, L25_lo)
                local C5_hi = bxor(L05_hi, L10_hi, L15_hi, L20_hi, L25_hi)

                local D_lo = bxor(C1_lo, C3_lo * 2 + (C3_hi % 2^32 - C3_hi % 2^31) / 2^31)
                local D_hi = bxor(C1_hi, C3_hi * 2 + (C3_lo % 2^32 - C3_lo % 2^31) / 2^31)

                local T0_lo = bxor(D_lo, L02_lo)
                local T0_hi = bxor(D_hi, L02_hi)
                local T1_lo = bxor(D_lo, L07_lo)
                local T1_hi = bxor(D_hi, L07_hi)
                local T2_lo = bxor(D_lo, L12_lo)
                local T2_hi = bxor(D_hi, L12_hi)
                local T3_lo = bxor(D_lo, L17_lo)
                local T3_hi = bxor(D_hi, L17_hi)
                local T4_lo = bxor(D_lo, L22_lo)
                local T4_hi = bxor(D_hi, L22_hi)

                L02_lo = (T1_lo % 2^32 - T1_lo % 2^20) / 2^20 + T1_hi * 2^12
                L02_hi = (T1_hi % 2^32 - T1_hi % 2^20) / 2^20 + T1_lo * 2^12
                L07_lo = (T3_lo % 2^32 - T3_lo % 2^19) / 2^19 + T3_hi * 2^13
                L07_hi = (T3_hi % 2^32 - T3_hi % 2^19) / 2^19 + T3_lo * 2^13
                L12_lo = T0_lo * 2 + (T0_hi % 2^32 - T0_hi % 2^31) / 2^31
                L12_hi = T0_hi * 2 + (T0_lo % 2^32 - T0_lo % 2^31) / 2^31
                L17_lo = T2_lo * 2^10 + (T2_hi % 2^32 - T2_hi % 2^22) / 2^22
                L17_hi = T2_hi * 2^10 + (T2_lo % 2^32 - T2_lo % 2^22) / 2^22
                L22_lo = T4_lo * 2^2 + (T4_hi % 2^32 - T4_hi % 2^30) / 2^30
                L22_hi = T4_hi * 2^2 + (T4_lo % 2^32 - T4_lo % 2^30) / 2^30

                D_lo = bxor(C2_lo, C4_lo * 2 + (C4_hi % 2^32 - C4_hi % 2^31) / 2^31)
                D_hi = bxor(C2_hi, C4_hi * 2 + (C4_lo % 2^32 - C4_lo % 2^31) / 2^31)

                T0_lo = bxor(D_lo, L03_lo)
                T0_hi = bxor(D_hi, L03_hi)
                T1_lo = bxor(D_lo, L08_lo)
                T1_hi = bxor(D_hi, L08_hi)
                T2_lo = bxor(D_lo, L13_lo)
                T2_hi = bxor(D_hi, L13_hi)
                T3_lo = bxor(D_lo, L18_lo)
                T3_hi = bxor(D_hi, L18_hi)
                T4_lo = bxor(D_lo, L23_lo)
                T4_hi = bxor(D_hi, L23_hi)

                L03_lo = (T2_lo % 2^32 - T2_lo % 2^21) / 2^21 + T2_hi * 2^11
                L03_hi = (T2_hi % 2^32 - T2_hi % 2^21) / 2^21 + T2_lo * 2^11
                L08_lo = (T4_lo % 2^32 - T4_lo % 2^3) / 2^3 + T4_hi * 2^29 % 2^32
                L08_hi = (T4_hi % 2^32 - T4_hi % 2^3) / 2^3 + T4_lo * 2^29 % 2^32
                L13_lo = T1_lo * 2^6 + (T1_hi % 2^32 - T1_hi % 2^26) / 2^26
                L13_hi = T1_hi * 2^6 + (T1_lo % 2^32 - T1_lo % 2^26) / 2^26
                L18_lo = T3_lo * 2^15 + (T3_hi % 2^32 - T3_hi % 2^17) / 2^17
                L18_hi = T3_hi * 2^15 + (T3_lo % 2^32 - T3_lo % 2^17) / 2^17
                L23_lo = (T0_lo % 2^32 - T0_lo % 2^2) / 2^2 + T0_hi * 2^30 % 2^32
                L23_hi = (T0_hi % 2^32 - T0_hi % 2^2) / 2^2 + T0_lo * 2^30 % 2^32

                D_lo = bxor(C3_lo, C5_lo * 2 + (C5_hi % 2^32 - C5_hi % 2^31) / 2^31)
                D_hi = bxor(C3_hi, C5_hi * 2 + (C5_lo % 2^32 - C5_lo % 2^31) / 2^31)

                T0_lo = bxor(D_lo, L04_lo)
                T0_hi = bxor(D_hi, L04_hi)
                T1_lo = bxor(D_lo, L09_lo)
                T1_hi = bxor(D_hi, L09_hi)
                T2_lo = bxor(D_lo, L14_lo)
                T2_hi = bxor(D_hi, L14_hi)
                T3_lo = bxor(D_lo, L19_lo)
                T3_hi = bxor(D_hi, L19_hi)
                T4_lo = bxor(D_lo, L24_lo)
                T4_hi = bxor(D_hi, L24_hi)

                L04_lo = T3_lo * 2^21 % 2^32 + (T3_hi % 2^32 - T3_hi % 2^11) / 2^11
                L04_hi = T3_hi * 2^21 % 2^32 + (T3_lo % 2^32 - T3_lo % 2^11) / 2^11
                L09_lo = T0_lo * 2^28 % 2^32 + (T0_hi % 2^32 - T0_hi % 2^4) / 2^4
                L09_hi = T0_hi * 2^28 % 2^32 + (T0_lo % 2^32 - T0_lo % 2^4) / 2^4
                L14_lo = T2_lo * 2^25 % 2^32 + (T2_hi % 2^32 - T2_hi % 2^7) / 2^7
                L14_hi = T2_hi * 2^25 % 2^32 + (T2_lo % 2^32 - T2_lo % 2^7) / 2^7
                L19_lo = (T4_lo % 2^32 - T4_lo % 2^8) / 2^8 + T4_hi * 2^24 % 2^32
                L19_hi = (T4_hi % 2^32 - T4_hi % 2^8) / 2^8 + T4_lo * 2^24 % 2^32
                L24_lo = (T1_lo % 2^32 - T1_lo % 2^9) / 2^9 + T1_hi * 2^23 % 2^32
                L24_hi = (T1_hi % 2^32 - T1_hi % 2^9) / 2^9 + T1_lo * 2^23 % 2^32

                D_lo = bxor(C4_lo, C1_lo * 2 + (C1_hi % 2^32 - C1_hi % 2^31) / 2^31)
                D_hi = bxor(C4_hi, C1_hi * 2 + (C1_lo % 2^32 - C1_lo % 2^31) / 2^31)

                T0_lo = bxor(D_lo, L05_lo)
                T0_hi = bxor(D_hi, L05_hi)
                T1_lo = bxor(D_lo, L10_lo)
                T1_hi = bxor(D_hi, L10_hi)
                T2_lo = bxor(D_lo, L15_lo)
                T2_hi = bxor(D_hi, L15_hi)
                T3_lo = bxor(D_lo, L20_lo)
                T3_hi = bxor(D_hi, L20_hi)
                T4_lo = bxor(D_lo, L25_lo)
                T4_hi = bxor(D_hi, L25_hi)

                L05_lo = T4_lo * 2^14 + (T4_hi % 2^32 - T4_hi % 2^18) / 2^18
                L05_hi = T4_hi * 2^14 + (T4_lo % 2^32 - T4_lo % 2^18) / 2^18
                L10_lo = T1_lo * 2^20 % 2^32 + (T1_hi % 2^32 - T1_hi % 2^12) / 2^12
                L10_hi = T1_hi * 2^20 % 2^32 + (T1_lo % 2^32 - T1_lo % 2^12) / 2^12
                L15_lo = T3_lo * 2^8 + (T3_hi % 2^32 - T3_hi % 2^24) / 2^24
                L15_hi = T3_hi * 2^8 + (T3_lo % 2^32 - T3_lo % 2^24) / 2^24
                L20_lo = T0_lo * 2^27 % 2^32 + (T0_hi % 2^32 - T0_hi % 2^5) / 2^5
                L20_hi = T0_hi * 2^27 % 2^32 + (T0_lo % 2^32 - T0_lo % 2^5) / 2^5
                L25_lo = (T2_lo % 2^32 - T2_lo % 2^25) / 2^25 + T2_hi * 2^7
                L25_hi = (T2_hi % 2^32 - T2_hi % 2^25) / 2^25 + T2_lo * 2^7

                D_lo = bxor(C5_lo, C2_lo * 2 + (C2_hi % 2^32 - C2_hi % 2^31) / 2^31)
                D_hi = bxor(C5_hi, C2_hi * 2 + (C2_lo % 2^32 - C2_lo % 2^31) / 2^31)

                T1_lo = bxor(D_lo, L06_lo)
                T1_hi = bxor(D_hi, L06_hi)
                T2_lo = bxor(D_lo, L11_lo)
                T2_hi = bxor(D_hi, L11_hi)
                T3_lo = bxor(D_lo, L16_lo)
                T3_hi = bxor(D_hi, L16_hi)
                T4_lo = bxor(D_lo, L21_lo)
                T4_hi = bxor(D_hi, L21_hi)

                L06_lo = T2_lo * 2^3 + (T2_hi % 2^32 - T2_hi % 2^29) / 2^29
                L06_hi = T2_hi * 2^3 + (T2_lo % 2^32 - T2_lo % 2^29) / 2^29
                L11_lo = T4_lo * 2^18 + (T4_hi % 2^32 - T4_hi % 2^14) / 2^14
                L11_hi = T4_hi * 2^18 + (T4_lo % 2^32 - T4_lo % 2^14) / 2^14
                L16_lo = (T1_lo % 2^32 - T1_lo % 2^28) / 2^28 + T1_hi * 2^4
                L16_hi = (T1_hi % 2^32 - T1_hi % 2^28) / 2^28 + T1_lo * 2^4
                L21_lo = (T3_lo % 2^32 - T3_lo % 2^23) / 2^23 + T3_hi * 2^9
                L21_hi = (T3_hi % 2^32 - T3_hi % 2^23) / 2^23 + T3_lo * 2^9

                L01_lo = bxor(D_lo, L01_lo)
                L01_hi = bxor(D_hi, L01_hi)
                L01_lo, L02_lo, L03_lo, L04_lo, L05_lo = bxor(L01_lo, band(-1 - L02_lo, L03_lo)), bxor(L02_lo, band(-1 - L03_lo, L04_lo)), bxor(L03_lo, band(-1 - L04_lo, L05_lo)), bxor(L04_lo, band(-1 - L05_lo, L01_lo)), bxor(L05_lo, band(-1 - L01_lo, L02_lo))
                L01_hi, L02_hi, L03_hi, L04_hi, L05_hi = bxor(L01_hi, band(-1 - L02_hi, L03_hi)), bxor(L02_hi, band(-1 - L03_hi, L04_hi)), bxor(L03_hi, band(-1 - L04_hi, L05_hi)), bxor(L04_hi, band(-1 - L05_hi, L01_hi)), bxor(L05_hi, band(-1 - L01_hi, L02_hi))
                L06_lo, L07_lo, L08_lo, L09_lo, L10_lo = bxor(L09_lo, band(-1 - L10_lo, L06_lo)), bxor(L10_lo, band(-1 - L06_lo, L07_lo)), bxor(L06_lo, band(-1 - L07_lo, L08_lo)), bxor(L07_lo, band(-1 - L08_lo, L09_lo)), bxor(L08_lo, band(-1 - L09_lo, L10_lo))
                L06_hi, L07_hi, L08_hi, L09_hi, L10_hi = bxor(L09_hi, band(-1 - L10_hi, L06_hi)), bxor(L10_hi, band(-1 - L06_hi, L07_hi)), bxor(L06_hi, band(-1 - L07_hi, L08_hi)), bxor(L07_hi, band(-1 - L08_hi, L09_hi)), bxor(L08_hi, band(-1 - L09_hi, L10_hi))
                L11_lo, L12_lo, L13_lo, L14_lo, L15_lo = bxor(L12_lo, band(-1 - L13_lo, L14_lo)), bxor(L13_lo, band(-1 - L14_lo, L15_lo)), bxor(L14_lo, band(-1 - L15_lo, L11_lo)), bxor(L15_lo, band(-1 - L11_lo, L12_lo)), bxor(L11_lo, band(-1 - L12_lo, L13_lo))
                L11_hi, L12_hi, L13_hi, L14_hi, L15_hi = bxor(L12_hi, band(-1 - L13_hi, L14_hi)), bxor(L13_hi, band(-1 - L14_hi, L15_hi)), bxor(L14_hi, band(-1 - L15_hi, L11_hi)), bxor(L15_hi, band(-1 - L11_hi, L12_hi)), bxor(L11_hi, band(-1 - L12_hi, L13_hi))
                L16_lo, L17_lo, L18_lo, L19_lo, L20_lo = bxor(L20_lo, band(-1 - L16_lo, L17_lo)), bxor(L16_lo, band(-1 - L17_lo, L18_lo)), bxor(L17_lo, band(-1 - L18_lo, L19_lo)), bxor(L18_lo, band(-1 - L19_lo, L20_lo)), bxor(L19_lo, band(-1 - L20_lo, L16_lo))
                L16_hi, L17_hi, L18_hi, L19_hi, L20_hi = bxor(L20_hi, band(-1 - L16_hi, L17_hi)), bxor(L16_hi, band(-1 - L17_hi, L18_hi)), bxor(L17_hi, band(-1 - L18_hi, L19_hi)), bxor(L18_hi, band(-1 - L19_hi, L20_hi)), bxor(L19_hi, band(-1 - L20_hi, L16_hi))
                L21_lo, L22_lo, L23_lo, L24_lo, L25_lo = bxor(L23_lo, band(-1 - L24_lo, L25_lo)), bxor(L24_lo, band(-1 - L25_lo, L21_lo)), bxor(L25_lo, band(-1 - L21_lo, L22_lo)), bxor(L21_lo, band(-1 - L22_lo, L23_lo)), bxor(L22_lo, band(-1 - L23_lo, L24_lo))
                L21_hi, L22_hi, L23_hi, L24_hi, L25_hi = bxor(L23_hi, band(-1 - L24_hi, L25_hi)), bxor(L24_hi, band(-1 - L25_hi, L21_hi)), bxor(L25_hi, band(-1 - L21_hi, L22_hi)), bxor(L21_hi, band(-1 - L22_hi, L23_hi)), bxor(L22_hi, band(-1 - L23_hi, L24_hi))
                L01_lo = bxor(L01_lo, RC_lo[round_idx])
                L01_hi = L01_hi + (RC_hi[round_idx]) -- RC_hi[] is either 0 or 0x80000000, so we could use fast addition instead of slow bxor
            end

            lanes_lo[1] = L01_lo
            lanes_hi[1] = L01_hi
            lanes_lo[2] = L02_lo
            lanes_hi[2] = L02_hi
            lanes_lo[3] = L03_lo
            lanes_hi[3] = L03_hi
            lanes_lo[4] = L04_lo
            lanes_hi[4] = L04_hi
            lanes_lo[5] = L05_lo
            lanes_hi[5] = L05_hi
            lanes_lo[6] = L06_lo
            lanes_hi[6] = L06_hi
            lanes_lo[7] = L07_lo
            lanes_hi[7] = L07_hi
            lanes_lo[8] = L08_lo
            lanes_hi[8] = L08_hi
            lanes_lo[9] = L09_lo
            lanes_hi[9] = L09_hi
            lanes_lo[10] = L10_lo
            lanes_hi[10] = L10_hi
            lanes_lo[11] = L11_lo
            lanes_hi[11] = L11_hi
            lanes_lo[12] = L12_lo
            lanes_hi[12] = L12_hi
            lanes_lo[13] = L13_lo
            lanes_hi[13] = L13_hi
            lanes_lo[14] = L14_lo
            lanes_hi[14] = L14_hi
            lanes_lo[15] = L15_lo
            lanes_hi[15] = L15_hi
            lanes_lo[16] = L16_lo
            lanes_hi[16] = L16_hi
            lanes_lo[17] = L17_lo
            lanes_hi[17] = L17_hi
            lanes_lo[18] = L18_lo
            lanes_hi[18] = L18_hi
            lanes_lo[19] = L19_lo
            lanes_hi[19] = L19_hi
            lanes_lo[20] = L20_lo
            lanes_hi[20] = L20_hi
            lanes_lo[21] = L21_lo
            lanes_hi[21] = L21_hi
            lanes_lo[22] = L22_lo
            lanes_hi[22] = L22_hi
            lanes_lo[23] = L23_lo
            lanes_hi[23] = L23_hi
            lanes_lo[24] = L24_lo
            lanes_hi[24] = L24_hi
            lanes_lo[25] = L25_lo
            lanes_hi[25] = L25_hi
        end
    end



    -- "block_size_in_bytes" is multiple of 8
    if type(digest_size) ~= "number" then
        -- arguments in SHAKE are swapped:
        --    NIST FIPS 202 defines SHAKE(message,num_bits)
        --    this module   defines SHAKE(num_bytes,message)
        -- it's easy to forget about this swap, hence the check
        error("Argument 'digest_size' must be a number", 2)
    end

    -- Create an instance (private objects for current calculation)
    local tail, lanes_lo, lanes_hi = "", table.create(25, 0), hi_factor_keccak == 0 and table.create(25, 0)
    local result

    --~     pad the input N using the pad function, yielding a padded bit string P with a length divisible by r (such that n = len(P)/r is integer),
    --~     break P into n consecutive r-bit pieces P0, ..., Pn-1 (last is zero-padded)
    --~     initialize the state S to a string of b 0 bits.
    --~     absorb the input into the state: For each block Pi,
    --~         extend Pi at the end by a string of c 0 bits, yielding one of length b,
    --~         bxor that with S and
    --~         apply the block permutation f to the result, yielding a new state S
    --~     initialize Z to be the empty string
    --~     while the length of Z is less than d:
    --~         append the first r bits of S to Z
    --~         if Z is still less than d bits long, apply f to S, yielding a new state S.
    --~     truncate Z to d bits
    local function partial(message_part)
        if message_part then
            local partLength = #message_part
            if tail then
                local offs = 0
                if tail ~= "" and #tail + partLength >= block_size_in_bytes then
                    offs = block_size_in_bytes - #tail
                    keccak_feed(lanes_lo, lanes_hi, tail .. string.sub(message_part, 1, offs), 0, block_size_in_bytes, block_size_in_bytes)
                    tail = ""
                end
                local size = partLength - offs
                local size_tail = size % block_size_in_bytes
                keccak_feed(lanes_lo, lanes_hi, message_part, offs, size - size_tail, block_size_in_bytes)
                tail = tail .. string.sub(message_part, partLength + 1 - size_tail)
                return partial
            else
                error("Adding more chunks is not allowed after receiving the result", 2)
            end
        else
            if tail then
                -- append the following bits to the message: for usual SHA3: 011(0*)1, for SHAKE: 11111(0*)1
                local gap_start = is_SHAKE and 31 or 6
                tail = tail .. (#tail + 1 == block_size_in_bytes and string.char(gap_start + 128) or string.char(gap_start) .. rep("\0", (-2 - #tail) % block_size_in_bytes) .. "\128")
                keccak_feed(lanes_lo, lanes_hi, tail, 0, #tail, block_size_in_bytes)
                tail = nil

                local lanes_used = 0
                local total_lanes = floor(block_size_in_bytes / 8)
                local qwords = {}

                local function get_next_qwords_of_digest(qwords_qty)
                    -- returns not more than 'qwords_qty' qwords ('qwords_qty' might be non-integer)
                    -- doesn't go across keccak-buffer boundary
                    -- block_size_in_bytes is a multiple of 8, so, keccak-buffer contains integer number of qwords
                    if lanes_used >= total_lanes then
                        keccak_feed(lanes_lo, lanes_hi, "\0\0\0\0\0\0\0\0", 0, 8, 8)
                        lanes_used = 0
                    end

                    qwords_qty = floor(math.min(qwords_qty, total_lanes - lanes_used))
                    if hi_factor_keccak ~= 0 then
                        for j = 1, qwords_qty do
                            qwords[j] = HEX64(lanes_lo[lanes_used + j - 1 + lanes_index_base])
                        end
                    else
                        for j = 1, qwords_qty do
                            qwords[j] = format("%08x", lanes_hi[lanes_used + j] % 4294967296) .. format("%08x", lanes_lo[lanes_used + j] % 4294967296)
                        end
                    end

                    lanes_used = lanes_used + qwords_qty
                    return string.gsub(table.concat(qwords, "", 1, qwords_qty), "(..)(..)(..)(..)(..)(..)(..)(..)", "%8%7%6%5%4%3%2%1"), qwords_qty * 8
                end

                local parts = {} -- digest parts
                local last_part, last_part_size = "", 0

                local function get_next_part_of_digest(bytes_needed)
                    -- returns 'bytes_needed' bytes, for arbitrary integer 'bytes_needed'
                    bytes_needed = bytes_needed or 1
                    if bytes_needed <= last_part_size then
                        last_part_size = last_part_size - bytes_needed
                        local part_size_in_nibbles = bytes_needed * 2
                        local result = string.sub(last_part, 1, part_size_in_nibbles)
                        last_part = string.sub(last_part, part_size_in_nibbles + 1)
                        return result
                    end

                    local parts_qty = 0
                    if last_part_size > 0 then
                        parts_qty = 1
                        parts[parts_qty] = last_part
                        bytes_needed = bytes_needed - last_part_size
                    end

                    -- repeats until the length is enough
                    while bytes_needed >= 8 do
                        local next_part, next_part_size = get_next_qwords_of_digest(bytes_needed / 8)
                        parts_qty = parts_qty + 1
                        parts[parts_qty] = next_part
                        bytes_needed = bytes_needed - next_part_size
                    end

                    if bytes_needed > 0 then
                        last_part, last_part_size = get_next_qwords_of_digest(1)
                        parts_qty = parts_qty + 1
                        parts[parts_qty] = get_next_part_of_digest(bytes_needed)
                    else
                        last_part, last_part_size = "", 0
                    end

                    return table.concat(parts, "", 1, parts_qty)
                end

                if digest_size < 0 then
                    result = get_next_part_of_digest
                else
                    result = get_next_part_of_digest(digest_size)
                end

            end

            return result
        end
    end

    if message then
        -- Actually perform calculations and return the SHA3 digest of a message
        return partial(message)()
    else
        -- Return function for chunk-by-chunk loading
        -- User should feed every chunk of input data as single argument to this function and finally get SHA3 digest by invoking this function without an argument
        return partial
    end
end

function RoCrypt.sha1(message)
    local md5_K, md5_sha1_H = {}, {0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0}

    local common_W = {}
    local function sha1_feed_64(H, str, offs, size)
        -- offs >= 0, size >= 0, size is multiple of 64
        local W = common_W
        local h1, h2, h3, h4, h5 = H[1], H[2], H[3], H[4], H[5]
        for pos = offs, offs + size - 1, 64 do
            for j = 1, 16 do
                pos = pos + 4
                local a, b, c, d = string.byte(str, pos - 3, pos)
                W[j] = ((a * 256 + b) * 256 + c) * 256 + d
            end

            for j = 17, 80 do
                W[j] = lrotate(bxor(W[j - 3], W[j - 8], W[j - 14], W[j - 16]), 1)
            end

            local a, b, c, d, e = h1, h2, h3, h4, h5
            for j = 1, 20 do
                local z = lrotate(a, 5) + band(b, c) + band(-1 - b, d) + 0x5A827999 + W[j] + e -- constant = math.floor(TWO_POW_30 * sqrt(2))
                e = d
                d = c
                c = rrotate(b, 2)
                b = a
                a = z
            end

            for j = 21, 40 do
                local z = lrotate(a, 5) + bxor(b, c, d) + 0x6ED9EBA1 + W[j] + e -- TWO_POW_30 * sqrt(3)
                e = d
                d = c
                c = rrotate(b, 2)
                b = a
                a = z
            end

            for j = 41, 60 do
                local z = lrotate(a, 5) + band(d, c) + band(b, bxor(d, c)) + 0x8F1BBCDC + W[j] + e -- TWO_POW_30 * sqrt(5)
                e = d
                d = c
                c = rrotate(b, 2)
                b = a
                a = z
            end

            for j = 61, 80 do
                local z = lrotate(a, 5) + bxor(b, c, d) + 0xCA62C1D6 + W[j] + e -- TWO_POW_30 * sqrt(10)
                e = d
                d = c
                c = rrotate(b, 2)
                b = a
                a = z
            end

            h1 = (a + h1) % 4294967296
            h2 = (b + h2) % 4294967296
            h3 = (c + h3) % 4294967296
            h4 = (d + h4) % 4294967296
            h5 = (e + h5) % 4294967296
        end

        H[1], H[2], H[3], H[4], H[5] = h1, h2, h3, h4, h5
    end

    -- Create an instance (private objects for current calculation)
    local H, length, queue = table.pack(table.unpack(md5_sha1_H)), 0, RoCrypt.utils.queue()

    local function partial(message_part)
        if message_part then
            length = length + #message_part
            queue.push(message_part)
            return partial
        else
            if queue.size() > 0 then
                local tail = queue.pop()
                local final_blocks = table.create(10) --{tail, "\128", string.rep("\0", (-9 - length) % 64 + 1)}
                final_blocks[1] = tail
                final_blocks[2] = "\128"
                final_blocks[3] = string.rep("\0", (-9 - length) % 64 + 1)

                -- Assuming user data length is shorter than (TWO_POW_53)-9 bytes
                -- TWO_POW_53 bytes = TWO_POW_56 bits, so "bit-counter" fits in 7 bytes
                length = length * (8 / (256^7)) -- convert "byte-counter" to "bit-counter" and move decimal point to the left
                for j = 4, 10 do
                    length = length % 1 * 256
                    final_blocks[j] = string.char(math.floor(length))
                end

                final_blocks = table.concat(final_blocks)
                sha1_feed_64(H, final_blocks, 0, #final_blocks)
                for j = 1, 5 do
                    H[j] = string.format("%08x", H[j] % 4294967296)
                end

                H = table.concat(H)
                queue.reset()
            end

            return H
        end
    end

    if message then
        -- Actually perform calculations and return the SHA-1 digest of a message
        return partial(message)()
    else
        -- Return function for chunk-by-chunk loading
        -- User should feed every chunk of input data as single argument to this function and finally get SHA-1 digest by invoking this function without an argument
        return partial
    end
end


function RoCrypt.sha224(message: string)
    if sha256ext then
        return sha256ext(224, message) 
    else
        sha_bootstrapper()
        return sha256ext(224, message)
    end
end

function RoCrypt.sha256(message: string)
    if sha256ext then
        return sha256ext(256, message) 
    else
        sha_bootstrapper()
        return sha256ext(256, message)
    end
end

function RoCrypt.sha384(message: string)
    if sha512ext then
        return sha512ext(384, message) 
    else
        sha_bootstrapper()
        return sha512ext(384, message)
    end
end

function RoCrypt.sha512(message: string)
    if sha512ext then
        return sha512ext(512, message) 
    else
        sha_bootstrapper()
        return sha512ext(512, message)
    end 
end

function RoCrypt.sha3_224(message: string)
    return keccak((1600 - 2 * 224) / 8, 224 / 8, false, message)
end

function RoCrypt.sha3_256(message: string)
    return keccak((1600 - 2 * 256) / 8, 256 / 8, false, message)
end

function RoCrypt.sha3_384(message: string)
    return keccak((1600 - 2 * 384) / 8, 384 / 8, false, message)
end

function RoCrypt.sha3_512(message: string)
    return keccak((1600 - 2 * 512) / 8, 512 / 8, false, message)
end

function RoCrypt.shake128(message:string , digest_size: number)
    return keccak((1600 - 2 * 128) / 8, digest_size/2, true, message)
end

function RoCrypt.shake256(message:string , digest_size: number)
    return keccak((1600 - 2 * 256) / 8, digest_size/2, true, message)
end

function RoCrypt.crc32(message: string, hex: boolean?) -- uses buffer
    local bmessage = buffer.fromstring(message)
    local crc = 0xFFFFFFFF
    local polynomial = 0xEDB88320

    for i = 0, buffer.len(bmessage) - 1 do
        local byte = buffer.readu8(bmessage, i)
        crc = bxor(crc, byte)

        for _ = 1, 8 do
            local mask = -band(crc, 1)
            crc = bxor(rshift(crc, 1), band(polynomial, mask))
        end
    end

    crc = bxor(crc, 0xFFFFFFFF)
    if hex == true then
        return string.format("%X", crc)
    else
        return crc
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
        clear(t)
        if #m == 1 and m[1] == 0 then
            return move(n, 1, #n, 1, t)
        elseif #n == 1 and n[1] == 0 then
            return move(m, 1, #m, 1, t)
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
        clear(t)
        local s = cmp(m, n)
        if s == nil then
            t[1] = 0
            return t, true
        end
        m, n = if s then m else n, if s then n else m
        if #m == 1 and m[1] == 0 then
            return move(n, 1, #n, 1, t), s
        elseif #n == 1 and n[1] == 0 then
            return move(m, 1, #m, 1, t), s
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
        clear(t)
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
                t[i + j], c = d % 16777216, floor(d / 16777216)
            end
            t[i] = c
        end
        while t[2] and t[1] == 0 do
            table.remove(t, 1)
        end

        return t
    end
    local function div(m, n, t1, t2, p1, p2)					-- Division and modulus
        clear	(t1)
        clear	(t2)
        t1[1] = 0
        move	(m, 1, #m, 1, t2)
        local s = true

        while cmp(t2, n) ~= false do
            clear(p1)
            if t2[1] < n[1] then
                p1[1] = floor((16777216 * t2[1] + t2[2]) / n[1])
                for i = 2, #t2 - #n do
                    p1[i] = 0
                end
            else
                p1[1] = floor(t2[1] / n[1])
                for i = 2, #t2 - #n + 1 do
                    p1[i] = 0
                end
            end

            clear(p2)
            move(t1, 1, #t1, 1, p2)
            _ = if s then add(p1, p2, t1) else sub(p1, p2, t1)
            clear(p2)
            mul(move(p1, 1, #p1, 1, p2), n, p1)
            clear(p2)
            move(t2, 1, #t2, 1, p2)
            _, s = sub(if s then p2 else p1, if s then p1 else p2, t2)
        end
        if not s then
            clear(p1)
            clear(p2)
            p2[1] = 1
            sub(move(t1, 1, #t1, 1, p1), p2, t1)
            clear(p1)
            sub(n, move(t2, 1, #t2, 1, p1), t2)
        end

        return t1, t2
    end
    local function lcm(m, n, t, p1, p2, p3, p4, p5)				-- Least common multiple
        clear(t)
        clear(p1)

        move(m, 1, #m, 1, t)
        move(n, 1, #n, 1, p1)
        while #p1 ~= 1 or p1[1] ~= 0 do 
            div(t, p1, p2, p3, p4, p5)
            clear(p2)
            move(t, 1, #t, 1, p2)

            clear(t)
            move(p1, 1, #p1, 1, t)
            clear(p1)
            move(p3, 1, #p3, 1, p1)
            clear(p3)
            move(p2, 1, #p2, 1, p3)
        end

        clear(p2)
        return div(mul(m, n, p1), move(t, 1, #t, 1, p2), t, p3, p4, p5)
    end --local e = 0
    local function pow(m, n, d, t, p1, p2, p3, p4, p5, p6)		-- Modular exponentiation
        clear	(t)
        clear	(p1)
        t[1] = 1
        move	(m, 1, #m, 1, p1)
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

            clear(p2)
            div(mul(move(p1, 1, #p1, 1, p2), p2, p3), d, p4, p1, p5, p6)
        end

        return t
    end
    local function inv(m, n, t, p1, p2, p3, p4, p5, p6, p7, p8) -- Modular multiplicative inverse
        clear	(t)
        clear	(p1)
        clear	(p2)
        clear	(p3)
        t[1] 	= 1
        p1[1] 	= 0
        move	(m, 1, #m, 1, p2)
        move	(n, 1, #n, 1, p3)
        local s1, s2, s3 = true, true, true

        while #p2 ~= 1 or p2[1] ~= 1 do
            div(p2, p3, p4, p5, p6, p7)
            clear	(p5)
            move	(p3, 1, #p3, 1, p5)
            div(p2, p5, p6, p3, p7, p8)
            clear	(p2)
            move	(p5, 1, #p5, 1, p2)
            clear	(p5)
            move	(p1, 1, #p1, 1, p5)

            s3 = s2
            mul(p1, p4, p6)
            if s1 == s2 then
                _, s2 = sub(t, p6, p1)
                s2 = if s1 then s2 else not s2
            else
                add(t, p6, p1)
                s2 = s1
            end
            move	(p5, 1, #p5, 1, t)
            s1 = s3
        end
        if not s1 then 
            clear(p1)
            sub(n, move(t, 1, #t, 1, p1), t)
        end

        return t
    end

    -- PROBABLY PRIME CHECKERS
    local function isDivisible	(a, p1, p2, p3, p4, p5) -- Checks if it is divisible by the first primes
        clear(p1)
        if #a == 1 and tfind(primes, a[1]) then
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
        clear(p1)
        clear(p3)
        if #a == 0 then
            return false
        elseif #a == 1 and tfind(primes, a[1]) then
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

        move(p2, 1, #p2, 1, p3)
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
                clear	(p1)
                p1[1] = 2
                clear	(p5)
                move	(p4, 1, #p4, 1, p5)
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
            a = floor(a)
            while a ~= 0 do
                table.insert(t, 1, a % 16777216)
                a = floor(a / 16777216)
            end
        elseif type(a) == "string" then
            if string.match(a, "^[0_]*$") then
                t[1] = 0
            elseif string.match(a, "^_*0_*[Xx][%x_]+$") or string.match(a, "^_*0_*[Bb][01_]+$") then
                local x = if string.match(a, "[Xx]") then 16 else 2
                n = string.gsub(string.match(a, "0_*.[0_]*(.+)"), "_", "")
                n = rep("0", - len(n) % if x == 16 then 6 else 24) .. n
                for i in gmatch(n, "(......" .. if x == 16 then ")" else "..................)")
                do
                    table.insert(t, tonumber(i, x))
                end
            elseif string.match(a, "^_*[%d_]*%.?[%d_]*$") then
                clear(p1)
                clear(p2)
                p1[1] = 10000000
                p2[1] = 1
                n = string.gsub(string.match(a, "_*[0_]*([%d_]*)%.?.-$"), "_", "")
                n = rep("0", - len(n) % 7) .. n
                for i in gmatch(reverse(n), "(.......)") do
                    clear(p3)
                    p3[1] = tonumber(reverse(i))
                    mul(p3, p2, p4)
                    clear(p3)
                    add(p4, move(t, 1, #t, 1, p3), t)
                    clear(p3)
                    mul(move(p2, 1, #p2, 1, p3), p1, p2)
                end
            else
                error("Unable to cast value to bigInt")
            end
        elseif type(a) == "table" then
            for i, j in ipairs(a) do
                assert(type(j) == "number" and floor(j) == j and 0 <= j and j < 16777216,
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
                local l = floor(tonumber(p) or 256)
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

                    clear(p1)
                    p1[1] = 2
                    while isDivisible(p, p2, p3, p4, p5, p6) do
                        add(move(p, 1, #p, 1, p2), p1, p)
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

                    clear(p1)
                    p1[1] = 2
                    while isDivisible(q, p2, p3, p4, p5, p6) do
                        add(move(q, 1, #q, 1, p2), p1, q)
                    end
                end
            else
                p, q = convertType(p, p1, p2, p3, p4), convertType(q, p1, p2, p3, p4)
                e = if e == nil then nil else convertType(e, p1, p2, p3, p4)
            end
            clear(p1)

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
                    clear(p5)
                    clear(p6)
                    p6[1] = 1
                    add(move(p4, 1, #p4, 1, p5), p6, p4)
                end
                clear(p5)
                sub(mul(p4, p, p6), move(p3, 1, #p3, 1, p5), p3)
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
                        a = floor	(a / 256)
                    end
                else
                    r, a = {if a < 0 then 128 else 0}, math.abs(a)
                    local e = math.round(math.log(a, 2))
                    r[2]  = (e + 1023) % 16 * 16
                    r[1] += floor((e + 1023) / 16)
                    a = (a * 2 ^ - e % 1) * 4503599627370496
                    for i = 1, 6 do
                        table.insert	(r, 3, a % 256)
                        a = floor	(a / 256)
                    end
                    r[2] += a
                end
            elseif type(a) == "string" then
                assert(a ~= "", "Unable to cast value to bytes")
                r = {}
                for i = 1, len(a), 7997 do
                    move({string.byte(a, i, i + 7996)}, 1, 7997, i, r)
                end
            elseif type(a) == "table" then
                assert(#a ~= 0, "Unable to cast value to bytes")
                r = {}
                for _, i in ipairs(a) do
                    assert(type(i) == "number" and floor(i) == i and 0 <= i and i < 256,
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




function RoCrypt.base64() -- uses buffer
    local CHAR_SET = buffer.fromstring("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")
    local base64charMap = buffer.create(256)
    for i = 0, 63 do
        buffer.writeu8(base64charMap, buffer.readu8(CHAR_SET, i), i)
    end

    local function encode(data)
        local dataBuffer = buffer.fromstring(data)
        local dataLength = buffer.len(dataBuffer)
        local outputLength = math.ceil(dataLength / 3) * 4
        local outputBuffer = buffer.create(outputLength)
        local c = 0

        for i = 0, dataLength - 1, 3 do
            local b1 = buffer.readu8(dataBuffer, i)
            local b2 = (i + 1 < dataLength) and buffer.readu8(dataBuffer, i + 1) or 0
            local b3 = (i + 2 < dataLength) and buffer.readu8(dataBuffer, i + 2) or 0

            local c1 = rshift(b1, 2)
            local c2 = bor(lshift(band(b1, 3), 4), rshift(b2, 4))
            local c3 = bor(lshift(band(b2, 15), 2), rshift(b3, 6))
            local c4 = band(b3, 63)

            buffer.writeu8(outputBuffer, c, buffer.readu8(CHAR_SET, c1))
            buffer.writeu8(outputBuffer, c + 1, buffer.readu8(CHAR_SET, c2))
            buffer.writeu8(outputBuffer, c + 2, (i + 1 < dataLength) and buffer.readu8(CHAR_SET, c3) or 61)
            buffer.writeu8(outputBuffer, c + 3, (i + 2 < dataLength) and buffer.readu8(CHAR_SET, c4) or 61)
            c = c + 4
        end

        return buffer.tostring(outputBuffer)
    end

    local function decode(data)
        local dataBuffer = buffer.fromstring(data)
        local dataLength = buffer.len(dataBuffer)
        local outputLength = math.floor(dataLength / 4) * 3
        local outputBuffer = buffer.create(outputLength)
        local c = 0

        for i = 0, dataLength - 1, 4 do
            local c1 = buffer.readu8(base64charMap, buffer.readu8(dataBuffer, i))
            local c2 = buffer.readu8(base64charMap, buffer.readu8(dataBuffer, i + 1))
            local c3 = buffer.readu8(base64charMap, buffer.readu8(dataBuffer, i + 2))
            local c4 = buffer.readu8(base64charMap, buffer.readu8(dataBuffer, i + 3))

            buffer.writeu8(outputBuffer, c, bor(lshift(c1, 2), rshift(c2, 4)))
            if c3 ~= 64 then
                buffer.writeu8(outputBuffer, c + 1, bor(lshift(band(c2, 15), 4), rshift(c3, 2)))
                if c4 ~= 64 then
                    buffer.writeu8(outputBuffer, c + 2, bor(lshift(band(c3, 3), 6), c4))
                    c = c + 3
                else
                    c = c + 2
                end
            else
                c = c + 1
            end
        end

        return buffer.tostring(outputBuffer, 0, c)
    end

    return {
        encode = encode,
        decode = decode
    }
end



function RoCrypt.base91() -- uses buffer
    local CHAR_SET = buffer.fromstring([[ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%&()*+,./:;<=>?@[]^_`{|}~"]])
    local ENCODE_CHAR_SET = buffer.create(91)
    local DECODE_CHAR_SET = buffer.create(256)
    for i = 0, 90 do
        local char = buffer.readu8(CHAR_SET, i)
        buffer.writeu8(ENCODE_CHAR_SET, i, char)
        buffer.writeu8(DECODE_CHAR_SET, char, i)
    end

    local function encodeBase91(input)
        input = buffer.fromstring(input)
        local outputBuffer = buffer.create(math.ceil(buffer.len(input) * 1.2))
        local c, counter, numBits = 0, 0, 0


        for i = 0, buffer.len(input) - 1 do
            counter = bor(counter, lshift(buffer.readu8(input, i), numBits))
            numBits = numBits + 8
            if numBits > 13 then
                local entry = band(counter, 8191)
                if entry > 88 then
                    counter = rshift(counter, 13)
                    numBits = numBits - 13
                else
                    entry = band(counter, 16383)
                    counter = rshift(counter, 14)
                    numBits = numBits - 14
                end
                buffer.writeu8(outputBuffer, c, buffer.readu8(ENCODE_CHAR_SET, entry%91))
                buffer.writeu8(outputBuffer, c+1, buffer.readu8(ENCODE_CHAR_SET, floor(entry/91)))
                c = c + 2
            end
        end

        if numBits > 0 then
            buffer.writeu8(outputBuffer, c, buffer.readu8(ENCODE_CHAR_SET, counter%91))
            c = c + 1
            if numBits > 7 or counter > 90 then
                buffer.writeu8(outputBuffer, c, buffer.readu8(ENCODE_CHAR_SET, floor(counter/91)))
                c = c + 1
            end
        end

        return buffer.tostring(outputBuffer, 0, c)
    end

    local function decodeBase91(input)
        input = buffer.fromstring(input)

        local outputBuffer = buffer.create(buffer.len(input))
        local c = 0

        local counter = 0
        local numBits = 0
        local entry = -1

        for i = 0, buffer.len(input) - 1 do
            local byte = buffer.readu8(input, i)
            local decoded = buffer.readu8(DECODE_CHAR_SET, byte)
            if decoded then
                if entry == -1 then
                    entry = decoded
                else
                    entry = entry + decoded * 91
                    counter = bor(counter, lshift(entry, numBits))
                    if band(entry, 8191) > 88 then
                        numBits = numBits + 13
                    else
                        numBits = numBits + 14
                    end

                    while numBits > 7 do
                        buffer.writeu8(outputBuffer, c, counter % 256)
                        c = c + 1
                        counter = rshift(counter, 8)
                        numBits = numBits - 8
                    end
                    entry = -1
                end
            end
        end

        if entry ~= -1 then
            buffer.writeu8(outputBuffer, c, bor(counter, lshift(entry, numBits)) % 256)
            c = c + 1
        end

        return buffer.tostring(outputBuffer, 0, c)
    end

    return {
        encode = encodeBase91,
        decode = decodeBase91,
    }
end


function RoCrypt.md2(message: string)
    local queue = RoCrypt.utils.queue_buffer()
    local pi = "3"..persistent.pi(722)
    local piIndex = 1
    local function pi_prng(n)
        while true do
            local ml = {10, 100, 1000}
            local x, y
            if n <= ml[1] then
                x, y = tonumber(string.sub(pi, piIndex, piIndex)), ml[1]
                piIndex += 1
            elseif n <= ml[2] then
                x, y = tonumber(string.sub(pi, piIndex, piIndex + 1)), ml[2]
                piIndex += 2
            elseif n <= ml[3] then
                x, y = tonumber(string.sub(pi, piIndex, piIndex + 2)), ml[3]
                piIndex += 3
            else
            end

            if x < (n * math.floor(y / n)) then
                return x % n
            end
        end
    end
    local SUBST = {}
    for i = 1, 256 do
        SUBST[i] = i
    end

    for i = 2, 256 do
        local j = pi_prng(i)+1
        SUBST[j], SUBST[i] = SUBST[i], SUBST[j]

    end
    for i,_ in ipairs(SUBST) do
        SUBST[i] -= 1
    end



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

    for b in gmatch(message, ".") do
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

    return format(
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

    for b in gmatch(message, ".") do
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

    return format("%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x",
        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)
end

function RoCrypt.md5(message: string)
    local function safeAdd (x, y)
        if x==nil then x=0 end
        if y==nil then y=0 end
        local lsw = bit.band(x , 0xffff) + bit.band(y , 0xffff)
        local msw = bit.arshift(x , 16) + bit.arshift(y , 16) + bit.arshift(lsw , 16)
        return bit.bor( bit.lshift(msw , 16) , bit.band(lsw , 0xffff) )
    end
    local function md5cmn (q, a, b, x, s, t)
        return safeAdd(bit32.lrotate(safeAdd(safeAdd(a, q), safeAdd(x, t)), s), b)
    end
    local function md5ff (a, b, c, d, x, s, t)
        return md5cmn( bit.bor(bit.band(b , c) , bit.band(bit.bnot(b) , d) ), a, b, x, s, t)
    end
    local function md5gg (a, b, c, d, x, s, t)
        return md5cmn( bit.bor(bit.band(b , d) , bit.band(c , bit.bnot(d)) ), a, b, x, s, t)
    end
    local function md5hh (a, b, c, d, x, s, t)
        return md5cmn( bit.bxor(b , c , d), a, b, x, s, t)
    end
    local function md5ii (a, b, c, d, x, s, t)
        return md5cmn( bit.bxor(c , bit.bor( b , bit.bnot(d) ) ), a, b, x, s, t)
    end

    local function binlMD5 (x, len)
        --append padding
        x[1+bit.arshift(len , 5)] = bit.bor( x[1+bit.arshift(len , 5)] , bit.lshift(0x80 , (len % 32)) )
        x[1+bit.lshift(bit.rshift( len + 64 , 9 ) , 4) + 14] = len

        local i, olda, oldb, oldc, oldd
        local a = 1732584193
        local b = -271733879
        local c = -1732584194
        local d = 271733878

        for i = 1,#x,16 do
            olda = a
            oldb = b
            oldc = c
            oldd = d

            a = md5ff(a, b, c, d, x[i], 7, -680876936)
            d = md5ff(d, a, b, c, x[i + 1], 12, -389564586)
            c = md5ff(c, d, a, b, x[i + 2], 17, 606105819)
            b = md5ff(b, c, d, a, x[i + 3], 22, -1044525330)
            a = md5ff(a, b, c, d, x[i + 4], 7, -176418897)
            d = md5ff(d, a, b, c, x[i + 5], 12, 1200080426)
            c = md5ff(c, d, a, b, x[i + 6], 17, -1473231341)
            b = md5ff(b, c, d, a, x[i + 7], 22, -45705983)
            a = md5ff(a, b, c, d, x[i + 8], 7, 1770035416)
            d = md5ff(d, a, b, c, x[i + 9], 12, -1958414417)
            c = md5ff(c, d, a, b, x[i + 10], 17, -42063)
            b = md5ff(b, c, d, a, x[i + 11], 22, -1990404162)
            a = md5ff(a, b, c, d, x[i + 12], 7, 1804603682)
            d = md5ff(d, a, b, c, x[i + 13], 12, -40341101)
            c = md5ff(c, d, a, b, x[i + 14], 17, -1502002290)
            b = md5ff(b, c, d, a, x[i + 15], 22, 1236535329)

            a = md5gg(a, b, c, d, x[i + 1], 5, -165796510)
            d = md5gg(d, a, b, c, x[i + 6], 9, -1069501632)
            c = md5gg(c, d, a, b, x[i + 11], 14, 643717713)
            b = md5gg(b, c, d, a, x[i], 20, -373897302)
            a = md5gg(a, b, c, d, x[i + 5], 5, -701558691)
            d = md5gg(d, a, b, c, x[i + 10], 9, 38016083)
            c = md5gg(c, d, a, b, x[i + 15], 14, -660478335)
            b = md5gg(b, c, d, a, x[i + 4], 20, -405537848)
            a = md5gg(a, b, c, d, x[i + 9], 5, 568446438)
            d = md5gg(d, a, b, c, x[i + 14], 9, -1019803690)
            c = md5gg(c, d, a, b, x[i + 3], 14, -187363961)
            b = md5gg(b, c, d, a, x[i + 8], 20, 1163531501)
            a = md5gg(a, b, c, d, x[i + 13], 5, -1444681467)
            d = md5gg(d, a, b, c, x[i + 2], 9, -51403784)
            c = md5gg(c, d, a, b, x[i + 7], 14, 1735328473)
            b = md5gg(b, c, d, a, x[i + 12], 20, -1926607734)

            a = md5hh(a, b, c, d, x[i + 5], 4, -378558)
            d = md5hh(d, a, b, c, x[i + 8], 11, -2022574463)
            c = md5hh(c, d, a, b, x[i + 11], 16, 1839030562)
            b = md5hh(b, c, d, a, x[i + 14], 23, -35309556)
            a = md5hh(a, b, c, d, x[i + 1], 4, -1530992060)
            d = md5hh(d, a, b, c, x[i + 4], 11, 1272893353)
            c = md5hh(c, d, a, b, x[i + 7], 16, -155497632)
            b = md5hh(b, c, d, a, x[i + 10], 23, -1094730640)
            a = md5hh(a, b, c, d, x[i + 13], 4, 681279174)
            d = md5hh(d, a, b, c, x[i], 11, -358537222)
            c = md5hh(c, d, a, b, x[i + 3], 16, -722521979)
            b = md5hh(b, c, d, a, x[i + 6], 23, 76029189)
            a = md5hh(a, b, c, d, x[i + 9], 4, -640364487)
            d = md5hh(d, a, b, c, x[i + 12], 11, -421815835)
            c = md5hh(c, d, a, b, x[i + 15], 16, 530742520)
            b = md5hh(b, c, d, a, x[i + 2], 23, -995338651)

            a = md5ii(a, b, c, d, x[i], 6, -198630844)
            d = md5ii(d, a, b, c, x[i + 7], 10, 1126891415)
            c = md5ii(c, d, a, b, x[i + 14], 15, -1416354905)
            b = md5ii(b, c, d, a, x[i + 5], 21, -57434055)
            a = md5ii(a, b, c, d, x[i + 12], 6, 1700485571)
            d = md5ii(d, a, b, c, x[i + 3], 10, -1894986606)
            c = md5ii(c, d, a, b, x[i + 10], 15, -1051523)
            b = md5ii(b, c, d, a, x[i + 1], 21, -2054922799)
            a = md5ii(a, b, c, d, x[i + 8], 6, 1873313359)
            d = md5ii(d, a, b, c, x[i + 15], 10, -30611744)
            c = md5ii(c, d, a, b, x[i + 6], 15, -1560198380)
            b = md5ii(b, c, d, a, x[i + 13], 21, 1309151649)
            a = md5ii(a, b, c, d, x[i + 4], 6, -145523070)
            d = md5ii(d, a, b, c, x[i + 11], 10, -1120210379)
            c = md5ii(c, d, a, b, x[i + 2], 15, 718787259)
            b = md5ii(b, c, d, a, x[i + 9], 21, -343485551)

            a = safeAdd(a, olda)
            b = safeAdd(b, oldb)
            c = safeAdd(c, oldc)
            d = safeAdd(d, oldd)
        end
        return {a, b, c, d}
    end

    local function binl2rstr (input)
        local i
        local output = {}
        local length32 = #input * 32
        for i = 0,length32-1,8 do
            table.insert(output,string.char( bit.band(bit.rshift( input[1+ bit.arshift(i , 5)] , i % 32 ) , 0xff ) ) )
        end
        return table.concat(output,'')
    end

    local function rstr2binl (input)
        local output = {}
        for i = 1,bit.arshift( string.len(input) , 2) do
            output[i] = 0
        end
        local length8 = string.len(input) * 8
        for i = 0,length8-1,8 do
            local p = 1+bit.arshift(i , 5);
            if output[p] == nil then output[p] = 0 end
            output[p] =  bit.bor( output[p], bit.lshift( bit.band(input:byte((i / 8)+1) , 0xff) , (i % 32) ) )
        end
        return output
    end

    local function rstrMD5 (s)
        return binl2rstr(binlMD5(rstr2binl(s), string.len(s) * 8))
    end





    return RoCrypt.utils.string2hex(binl2rstr(binlMD5(rstr2binl(message), string.len(message) * 8)))
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

        return format(fmt,
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

        return format(fmt,
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
            b10, b11, b12, b13, b14, b15, b16, b17, b18, b19)
    end



    init()
    update(message)
    finish()

    return asHex()

end

-- @ https://devforum.roblox.com/t/advanced-encryption-standard-in-luau/2009120
function RoCrypt.aes(message: any?)
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
            move		(c[1], 1, 4, 1, t)
            move		(c[2], 1, 4, 5, t)
            move		(c[3], 1, 4, 9, t)
            move		(c[4], 1, 4, 13, t)
        else
            for i = 1, #c / 4 do
                clear	(t[i])
                move	(c, i * 4 - 3, i * 4, 1, t[i])
            end
        end

        return t
    end
    local function xorBytes		(t, a, b) 		-- Returns bitwise bxor of all their bytes
        clear		(t)

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

            clear	(t)
            xorBytes	(w, move(w, 1, 4, 1, t), kc[#kc - is + 1])
            table.insert(kc, w)
        end

        clear		(t)
        for i = 1, #kc / 4 do
            table.insert(t, {})
            move	(kc, i * 4 - 3, i * 4, 1, t[#t])
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

            for i = 1, len(a), 7997 do
                move({string.byte(a, i, i + 7996)}, 1, 7997, i, r)
            end
            return r
        elseif type(a) == "table" then
            for _, i in ipairs(a) do
                assert(type(i) == "number" and floor(i) == i and 0 <= i and i < 256,
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
            s = floor(tonumber(s) or 1)
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
                move(plainText, i, i + 15, 1, k)
                move(encrypt(key, km, k, s, t), 1, 16, i, b)
            end

            return RoCrypt.utils.bytes2hex(b)
        end,
        decrypt_ECB = function(key : any, cipherText : any) 								: any
            if not RoCrypt.utils.isStringHex(cipherText) then 
                return error("Input text must be a hexadecimal string!")     
            end
            cipherText = RoCrypt.utils.hex2bytes(cipherText)

            local km
            key, cipherText, km = init(key, cipherText)

            local b, k, s, t = {}, {}, {{}, {}, {}, {}}, {}
            for i = 1, #cipherText, 16 do
                move(cipherText, i, i + 15, 1, k)
                move(decrypt(key, km, k, s, t), 1, 16, i, b)
            end

            return RoCrypt.utils.bytes2string(b)
        end,
        -- Cipher block chaining (CBC)
        encrypt_CBC = function(key : bytes, plainText : bytes, initVector : bytes?) 			: bytes
            local km
            key, plainText, km, initVector = init(key, plainText, false, initVector)

            local b, k, p, s, t = {}, {}, initVector, {{}, {}, {}, {}}, {}
            for i = 1, #plainText, 16 do
                move(plainText, i, i + 15, 1, k)
                move(encrypt(key, km, xorBytes(t, k, p), s, p), 1, 16, i, b)
            end

            return RoCrypt.utils.bytes2hex(b)
        end,
        decrypt_CBC = function(key : bytes, cipherText : bytes, initVector : bytes?) 			: bytes
            if not RoCrypt.utils.isStringHex(cipherText) then 
                return error("Input text must be a hexadecimal string!")     
            end            
            cipherText = RoCrypt.utils.hex2bytes(cipherText)
            local km
            key, cipherText, km, initVector = init(key, cipherText, false, initVector)


            local b, k, p, s, t = {}, {}, initVector, {{}, {}, {}, {}}, {}
            for i = 1, #cipherText, 16 do
                move(cipherText, i, i + 15, 1, k)
                move(xorBytes(k, decrypt(key, km, k, s, t), p), 1, 16, i, b)
                move(cipherText, i, i + 15, 1, p)
            end

            return  RoCrypt.utils.bytes2string(b)
        end,
        -- Propagating cipher block chaining (PCBC)
        encrypt_PCBC = function(key : bytes, plainText : bytes, initVector : bytes?) 			: bytes
            local km
            key, plainText, km, initVector = init(key, plainText, false, initVector)

            local b, k, c, p, s, t = {}, {}, initVector, table.create(16, 0), {{}, {}, {}, {}}, {}
            for i = 1, #plainText, 16 do
                move(plainText, i, i + 15, 1, k)
                move(encrypt(key, km, xorBytes(k, xorBytes(t, c, k), p), s, c), 1, 16, i, b)
                move(plainText, i, i + 15, 1, p)
            end

            return b
        end,
        decrypt_PCBC = function(key : bytes, cipherText : bytes, initVector : bytes?) 			: bytes
            if not RoCrypt.utils.isStringHex(cipherText) then 
                return error("Input text must be a hexadecimal string!")     
            end
            local km
            key, cipherText, km, initVector = init(key, cipherText, false, initVector)

            local b, k, c, p, s, t = {}, {}, initVector, table.create(16, 0), {{}, {}, {}, {}}, {}
            for i = 1, #cipherText, 16 do
                move(cipherText, i, i + 15, 1, k)
                move(xorBytes(p, decrypt(key, km, k, s, t), xorBytes(k, c, p)), 1, 16, i, b)
                move(cipherText, i, i + 15, 1, c)
            end

            return b
        end,
        -- Cipher feedback (CFB)
        encrypt_CFB = function(key, plainText, initVector : bytes?, segmentSize : number?)


            local km
            key, plainText, km, initVector, segmentSize = init(key, plainText, false, initVector,
                if segmentSize == nil then 1 else segmentSize)

            local b, k, p, q, s, t = {}, {}, initVector, {}, {{}, {}, {}, {}}, {}
            for i = 1, #plainText, segmentSize do
                move(plainText, i, i + segmentSize - 1, 1, k)
                move(xorBytes(q, encrypt(key, km, p, s, t), k), 1, segmentSize, i, b)
                for j = 16, segmentSize + 1, - 1 do
                    table.insert(q, 1, p[j])
                end
                move(q, 1, 16, 1, p)
            end

            return RoCrypt.utils.bytes2hex(b)
        end,
        decrypt_CFB = function(key, cipherText, initVector : bytes, segmentSize : number?)
            if not RoCrypt.utils.isStringHex(cipherText) then 
                return error("Input text must be a hexadecimal string!")     
            end
            cipherText = RoCrypt.utils.hex2bytes(cipherText)
            local km
            key, cipherText, km, initVector, segmentSize = init(key, cipherText, false, initVector,
                if segmentSize == nil then 1 else segmentSize)

            local b, k, p, q, s, t = {}, {}, initVector, {}, {{}, {}, {}, {}}, {}
            for i = 1, #cipherText, segmentSize do
                move(cipherText, i, i + segmentSize - 1, 1, k)
                move(xorBytes(q, encrypt(key, km, p, s, t), k), 1, segmentSize, i, b)
                for j = 16, segmentSize + 1, - 1 do
                    table.insert(k, 1, p[j])
                end
                move(k, 1, 16, 1, p)
            end

            return RoCrypt.utils.bytes2string(b)
        end,
        -- Output feedback (OFB)
        encrypt_OFB = function(key : bytes, plainText : bytes, initVector : bytes?) 			: bytes
            local km
            key, plainText, km, initVector = init(key, plainText, false, initVector)

            local b, k, p, s, t = {}, {}, initVector, {{}, {}, {}, {}}, {}
            for i = 1, #plainText, 16 do
                move(plainText, i, i + 15, 1, k)
                move(encrypt(key, km, p, s, t), 1, 16, 1, p)
                move(xorBytes(t, k, p), 1, 16, i, b)
            end

            return RoCrypt.utils.bytes2hex(b)
        end,
        decrypt_OFB = function(key : bytes, plainText : bytes, initVector : bytes?) 			: bytes
            if not RoCrypt.utils.isStringHex(plainText) then 
                return error("Input text must be a hexadecimal string!")     
            end
            plainText = RoCrypt.utils.hex2bytes(plainText)
            local km
            key, plainText, km, initVector = init(key, plainText, false, initVector)

            local b, k, p, s, t = {}, {}, initVector, {{}, {}, {}, {}}, {}
            for i = 1, #plainText, 16 do
                move(plainText, i, i + 15, 1, k)
                move(encrypt(key, km, p, s, t), 1, 16, 1, p)
                move(xorBytes(t, k, p), 1, 16, i, b)
            end

            return RoCrypt.utils.bytes2string(b)
        end,
        -- Counter (CTR)
        encrypt_CTR = function(key, plainText, counter : ((bytes) -> bytes) | bytes | { [
            string]: any }?) : bytes



            local km
            key, plainText, km, counter = init(key, plainText, true, counter)

            local b, k, c, s, t, r, n = {}, {}, {}, {{}, {}, {}, {}}, {}, type(counter) == "table", nil
            for i = 1, #plainText, 16 do
                if r then
                    if i > 1 and incBytes(counter.InitValue, counter.LittleEndian) then
                        move(counter.InitOverflow, 1, 16, 1, counter.InitValue)
                    end
                    clear	(c)
                    move	(counter.Prefix, 1, #counter.Prefix, 1, c)
                    move	(counter.InitValue, 1, counter.Length, #c + 1, c)
                    move	(counter.Suffix, 1, #counter.Suffix, #c + 1, c)
                else
                    n = convertType(counter(c, (i + 15) / 16))
                    assert		(#n == 16, "Counter must be 16 bytes long")
                    move	(n, 1, 16, 1, c)
                end
                move(plainText, i, i + 15, 1, k)
                move(xorBytes(c, encrypt(key, km, c, s, t), k), 1, 16, i, b)
            end

            return RoCrypt.utils.bytes2hex(b)
        end,
        decrypt_CTR = function(key, plainText, counter : ((bytes) -> bytes) | bytes | { [
            string]: any }?) : bytes

            if not RoCrypt.utils.isStringHex(plainText) then 
                return error("Input text must be a hexadecimal string!")     
            end

            plainText = RoCrypt.utils.hex2bytes(plainText)

            local km
            key, plainText, km, counter = init(key, plainText, true, counter)

            local b, k, c, s, t, r, n = {}, {}, {}, {{}, {}, {}, {}}, {}, type(counter) == "table", nil
            for i = 1, #plainText, 16 do
                if r then
                    if i > 1 and incBytes(counter.InitValue, counter.LittleEndian) then
                        move(counter.InitOverflow, 1, 16, 1, counter.InitValue)
                    end
                    clear	(c)
                    move	(counter.Prefix, 1, #counter.Prefix, 1, c)
                    move	(counter.InitValue, 1, counter.Length, #c + 1, c)
                    move	(counter.Suffix, 1, #counter.Suffix, #c + 1, c)
                else
                    n = convertType(counter(c, (i + 15) / 16))
                    assert		(#n == 16, "Counter must be 16 bytes long")
                    move	(n, 1, 16, 1, c)
                end
                move(plainText, i, i + 15, 1, k)
                move(xorBytes(c, encrypt(key, km, c, s, t), k), 1, 16, i, b)
            end

            return RoCrypt.utils.bytes2string(b)
        end

    } -- Returns the library
end


function RoCrypt.hmac(hash_func: any, key: any, message: any)
    local AND_of_two_bytes = {[0] = 0}  -- look-up table (256*256 entries)
    local idx = 0
    for y = 0, 127 * 256, 256 do
        for x = y, y + 127 do
            x = AND_of_two_bytes[x] * 2
            AND_of_two_bytes[idx] = x
            AND_of_two_bytes[idx + 1] = x
            AND_of_two_bytes[idx + 256] = x
            AND_of_two_bytes[idx + 257] = x + 1
            idx = idx + 2
        end
        idx = idx + 256
    end

    local function bxor_BYTE(x, y)
        return x + y - 2 * AND_of_two_bytes[x + y * 256]
    end

    local function pad_and_xor(str, result_length, byte_for_xor)
        return string.gsub(str, ".",
            function(c)
                return char(bxor_BYTE(byte(c), byte_for_xor))
            end
        )..string.rep(char(byte_for_xor), result_length - #str)
    end

    local hex_to_bin
    do
        function hex_to_bin(hex_string)
            return (string.gsub(hex_string, "%x%x",
                function (hh)
                    return char(tonumber(hh, 16))
                end
                ))
        end
    end

    local  block_size_for_HMAC = {
        [RoCrypt.md5]        =  64,
        [RoCrypt.sha1]       =  64,
        [RoCrypt.sha224]     =  64,
        [RoCrypt.sha256]     =  64,
        [RoCrypt.sha384]     = 128,
        [RoCrypt.sha512]     = 128,
        [RoCrypt.sha3_224]   = 144,  -- (1600 - 2 * 224) / 8
        [RoCrypt.sha3_256]   = 136,  -- (1600 - 2 * 256) / 8
        [RoCrypt.sha3_384]   = 104,  -- (1600 - 2 * 384) / 8
        [RoCrypt.sha3_512]   =  72,  -- (1600 - 2 * 512) / 8
    }
    -- Create an instance (private objects for current calculation)
    local block_size = block_size_for_HMAC[hash_func]
    if not block_size then
        error("This function is currently unsupported by HMAC.", 2)
    end
    if #key > block_size then
        key = hex_to_bin(hash_func(key))
    end
    local append = hash_func()(pad_and_xor(key, block_size, 0x36))
    local result

    local function partial(message_part)
        if not message_part then
            result = result or hash_func(pad_and_xor(key, block_size, 0x5C)..hex_to_bin(append()))
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
        return partial(message)()
    else
        -- Return function for chunk-by-chunk loading of a message
        -- User should feed every chunk of the message as single argument to this function and finally get HMAC by invoking this function without an argument
        return partial
    end
end




function RoCrypt.des()
    local Array = RoCrypt.utils.array();


    local IN_P = {
        58, 50, 42, 34, 26, 18, 10,  2,
        60, 52, 44, 36, 28, 20, 12,  4,
        62, 54, 46, 38, 30, 22, 14,  6,
        64, 56, 48, 40, 32, 24, 16,  8,
        57, 49, 41, 33, 25, 17,  9,  1,
        59, 51, 43, 35, 27, 19, 11,  3,
        61, 53, 45, 37, 29, 21, 13,  5,
        63, 55, 47, 39, 31, 23, 15,  7};

    local OUT_P = {
        40,  8, 48, 16, 56, 24, 64, 32,
        39,  7, 47, 15, 55, 23, 63, 31,
        38,  6, 46, 14, 54, 22, 62, 30,
        37,  5, 45, 13, 53, 21, 61, 29,
        36,  4, 44, 12, 52, 20, 60, 28,
        35,  3, 43, 11, 51, 19, 59, 27,
        34,  2, 42, 10, 50, 18, 58, 26,
        33,  1, 41,  9, 49, 17, 57, 25};

    -- add 32 to each because we do the expansion on the full LR table, not just R
    local EBIT = {
        32 + 32,  1 + 32,  2 + 32,  3 + 32,  4 + 32,  5 + 32,  4 + 32,  5 + 32,  6 + 32,  7 + 32,  8 + 32,  9 + 32,
        8 + 32,  9 + 32, 10 + 32, 11 + 32, 12 + 32, 13 + 32, 12 + 32, 13 + 32, 14 + 32, 15 + 32, 16 + 32, 17 + 32,
        16 + 32, 17 + 32, 18 + 32, 19 + 32, 20 + 32, 21 + 32, 20 + 32, 21 + 32, 22 + 32, 23 + 32, 24 + 32, 25 + 32,
        24 + 32, 25 + 32, 26 + 32, 27 + 32, 28 + 32, 29 + 32, 28 + 32, 29 + 32, 30 + 32, 31 + 32, 32 + 32,  1 + 32, };

    local LR_SWAP = {
        33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
        49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32};

    local PC1 = {
        57, 49, 41, 33, 25, 17, 9, 1, 58, 50, 42, 34, 26, 18,
        10, 2, 59, 51, 43, 35, 27, 19, 11, 3, 60, 52, 44, 36,
        63, 55, 47, 39, 31, 23, 15, 7, 62, 54, 46, 38, 30, 22,
        14, 6, 61, 53, 45, 37, 29, 21, 13, 5, 28, 20, 12, 4};

    local PC2 = {
        14, 17, 11, 24, 1, 5, 3, 28, 15, 6, 21, 10,
        23, 19, 12, 4, 26, 8, 16, 7, 27, 20, 13, 2,
        41, 52, 31, 37, 47, 55, 30, 40, 51, 45, 33, 48,
        44, 49, 39, 56, 34, 53, 46, 42, 50, 36, 29, 32};

    local KS1 = {
        2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 1,
        30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 29};
    local KS2 = KS1;

    local KS3 = {
        3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 1, 2,
        31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 29, 30};

    local KS4  = KS3;
    local KS5  = KS3;
    local KS6  = KS3;
    local KS7  = KS3;
    local KS8  = KS3;
    local KS9  = KS1;
    local KS10 = KS3;
    local KS11 = KS3;
    local KS12 = KS3;
    local KS13 = KS3;
    local KS14 = KS3;
    local KS15 = KS3;
    local KS16 = KS1;

    local SBOX1 = { 14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7,
        0, 15, 7, 4, 14, 2, 13, 1, 10, 6, 12, 11, 9, 5, 3, 8,
        4, 1, 14, 8, 13, 6, 2, 11, 15, 12, 9, 7, 3, 10, 5, 0,
        15, 12, 8, 2, 4, 9, 1, 7, 5, 11, 3, 14, 10, 0, 6, 13};

    local SBOX2 = { 15, 1, 8, 14, 6, 11, 3, 4, 9, 7, 2, 13, 12, 0, 5, 10,
        3, 13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5,
        0, 14, 7, 11, 10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15,
        13, 8, 10, 1, 3, 15, 4, 2, 11, 6, 7, 12, 0, 5, 14, 9};

    local SBOX3 = { 10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8,
        13, 7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1,
        13, 6, 4, 9, 8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7,
        1, 10, 13, 0, 6, 9, 8, 7, 4, 15, 14, 3, 11, 5, 2, 12};

    local SBOX4 = { 7, 13, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15,
        13, 8, 11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9,
        10, 6, 9, 0, 12, 11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4,
        3, 15, 0, 6, 10, 1, 13, 8, 9, 4, 5, 11, 12, 7, 2, 14};

    local SBOX5 = { 2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9,
        14, 11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6,
        4, 2, 1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14,
        11, 8, 12, 7, 1, 14, 2, 13, 6, 15, 0, 9, 10, 4, 5, 3};

    local SBOX6 = { 12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11,
        10, 15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8,
        9, 14, 15, 5, 2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6,
        4, 3, 2, 12, 9, 5, 15, 10, 11, 14, 1, 7, 6, 0, 8, 13};

    local SBOX7 = { 4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1,
        13, 0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6,
        1, 4, 11, 13, 12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2,
        6, 11, 13, 8, 1, 4, 10, 7, 9, 5, 0, 15, 14, 2, 3, 12};

    local SBOX8 = { 13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7,
        1, 15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2,
        7, 11, 4, 1, 9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8,
        2, 1, 14, 7, 4, 10, 8, 13, 15, 12, 9, 0, 3, 5, 6, 11};

    local ROUND_P = { 16, 7, 20, 21, 29, 12, 28, 17, 1, 15, 23, 26, 5, 18, 31, 10,
        2, 8, 24, 14, 32, 27, 3, 9, 19, 13, 30, 6, 22, 11, 4, 25};

    local permute = Array.permute;

    local unpackBytes = function(bytes)
        local bits = {};

        for _, b in pairs(bytes) do
            table.insert(bits, rshift(band(b, 0x80), 7));
            table.insert(bits, rshift(band(b, 0x40), 6));
            table.insert(bits, rshift(band(b, 0x20), 5));
            table.insert(bits, rshift(band(b, 0x10), 4));
            table.insert(bits, rshift(band(b, 0x08), 3));
            table.insert(bits, rshift(band(b, 0x04), 2));
            table.insert(bits, rshift(band(b, 0x02), 1));
            table.insert(bits,      band(b, 0x01)   );
        end

        return bits;
    end

    local packBytes = function(bits)
        local bytes = {}

        for k, _ in pairs(bits) do
            local index = math.floor((k - 1) / 8) + 1;
            local shift = 7 - math.fmod((k - 1), 8);

            local bit = bits[k];
            local byte = bytes[index];

            if not byte then byte = 0x00; end
            byte = bor(byte, lshift(bit, shift));
            bytes[index] = byte;
        end

        return bytes;
    end

    local mix = function(LR, key)

        local ER = permute(LR, EBIT);

        for k, _ in pairs(ER) do
            ER[k] = bxor(ER[k], key[k]);
        end

        local FRK = {};

        local S = 0x00;
        S = bor(S, ER[1]); S = lshift(S, 1);
        S = bor(S, ER[6]); S = lshift(S, 1);
        S = bor(S, ER[2]); S = lshift(S, 1);
        S = bor(S, ER[3]); S = lshift(S, 1);
        S = bor(S, ER[4]); S = lshift(S, 1);
        S = bor(S, ER[5]); S = S + 1;
        S = SBOX1[S];

        FRK[1] = rshift(band(S, 0x08), 3);
        FRK[2] = rshift(band(S, 0x04), 2);
        FRK[3] = rshift(band(S, 0x02), 1);
        FRK[4] = band(S, 0x01);


        S = 0x00;
        S = bor(S, ER[1 + 6]); S = lshift(S, 1);
        S = bor(S, ER[6 + 6]); S = lshift(S, 1);
        S = bor(S, ER[2 + 6]); S = lshift(S, 1);
        S = bor(S, ER[3 + 6]); S = lshift(S, 1);
        S = bor(S, ER[4 + 6]); S = lshift(S, 1);
        S = bor(S, ER[5 + 6]); S = S + 1;
        S = SBOX2[S];

        FRK[5] = rshift(band(S, 0x08), 3);
        FRK[6] = rshift(band(S, 0x04), 2);
        FRK[7] = rshift(band(S, 0x02), 1);
        FRK[8] = band(S, 0x01);


        S = 0x00;
        S = bor(S, ER[1 + 12]); S = lshift(S, 1);
        S = bor(S, ER[6 + 12]); S = lshift(S, 1);
        S = bor(S, ER[2 + 12]); S = lshift(S, 1);
        S = bor(S, ER[3 + 12]); S = lshift(S, 1);
        S = bor(S, ER[4 + 12]); S = lshift(S, 1);
        S = bor(S, ER[5 + 12]); S = S + 1;
        S = SBOX3[S];

        FRK[9] = rshift(band(S, 0x08), 3);
        FRK[10] = rshift(band(S, 0x04), 2);
        FRK[11] = rshift(band(S, 0x02), 1);
        FRK[12] = band(S, 0x01);


        S = 0x00;
        S = bor(S, ER[1 + 18]); S = lshift(S, 1);
        S = bor(S, ER[6 + 18]); S = lshift(S, 1);
        S = bor(S, ER[2 + 18]); S = lshift(S, 1);
        S = bor(S, ER[3 + 18]); S = lshift(S, 1);
        S = bor(S, ER[4 + 18]); S = lshift(S, 1);
        S = bor(S, ER[5 + 18]); S = S + 1;
        S = SBOX4[S];

        FRK[13] = rshift(band(S, 0x08), 3);
        FRK[14] = rshift(band(S, 0x04), 2);
        FRK[15] = rshift(band(S, 0x02), 1);
        FRK[16] = band(S, 0x01);


        S = 0x00;
        S = bor(S, ER[1 + 24]); S = lshift(S, 1);
        S = bor(S, ER[6 + 24]); S = lshift(S, 1);
        S = bor(S, ER[2 + 24]); S = lshift(S, 1);
        S = bor(S, ER[3 + 24]); S = lshift(S, 1);
        S = bor(S, ER[4 + 24]); S = lshift(S, 1);
        S = bor(S, ER[5 + 24]); S = S + 1;
        S = SBOX5[S];

        FRK[17] = rshift(band(S, 0x08), 3);
        FRK[18] = rshift(band(S, 0x04), 2);
        FRK[19] = rshift(band(S, 0x02), 1);
        FRK[20] = band(S, 0x01);


        S = 0x00;
        S = bor(S, ER[1 + 30]); S = lshift(S, 1);
        S = bor(S, ER[6 + 30]); S = lshift(S, 1);
        S = bor(S, ER[2 + 30]); S = lshift(S, 1);
        S = bor(S, ER[3 + 30]); S = lshift(S, 1);
        S = bor(S, ER[4 + 30]); S = lshift(S, 1);
        S = bor(S, ER[5 + 30]); S = S + 1;
        S = SBOX6[S];

        FRK[21] = rshift(band(S, 0x08), 3);
        FRK[22] = rshift(band(S, 0x04), 2);
        FRK[23] = rshift(band(S, 0x02), 1);
        FRK[24] = band(S, 0x01);


        S = 0x00;
        S = bor(S, ER[1 + 36]); S = lshift(S, 1);
        S = bor(S, ER[6 + 36]); S = lshift(S, 1);
        S = bor(S, ER[2 + 36]); S = lshift(S, 1);
        S = bor(S, ER[3 + 36]); S = lshift(S, 1);
        S = bor(S, ER[4 + 36]); S = lshift(S, 1);
        S = bor(S, ER[5 + 36]); S = S + 1;
        S = SBOX7[S];

        FRK[25] = rshift(band(S, 0x08), 3);
        FRK[26] = rshift(band(S, 0x04), 2);
        FRK[27] = rshift(band(S, 0x02), 1);
        FRK[28] = band(S, 0x01);


        S = 0x00;
        S = bor(S, ER[1 + 42]); S = lshift(S, 1);
        S = bor(S, ER[6 + 42]); S = lshift(S, 1);
        S = bor(S, ER[2 + 42]); S = lshift(S, 1);
        S = bor(S, ER[3 + 42]); S = lshift(S, 1);
        S = bor(S, ER[4 + 42]); S = lshift(S, 1);
        S = bor(S, ER[5 + 42]); S = S + 1;
        S = SBOX8[S];

        FRK[29] = rshift(band(S, 0x08), 3);
        FRK[30] = rshift(band(S, 0x04), 2);
        FRK[31] = rshift(band(S, 0x02), 1);
        FRK[32] = band(S, 0x01);

        FRK = permute(FRK, ROUND_P);

        return FRK;
    end

    local DES = {};

    DES.blockSize = 8;

    DES.encrypt = function(keyBlock, inputBlock)

        local LR = unpackBytes(inputBlock);
        local keyBits = unpackBytes(keyBlock);


        local CD = permute(keyBits, PC1);

        --key schedule
        CD = permute(CD, KS1); local KEY1 = permute(CD, PC2);
        CD = permute(CD, KS2); local KEY2 = permute(CD, PC2);
        CD = permute(CD, KS3); local KEY3 = permute(CD, PC2);
        CD = permute(CD, KS4); local KEY4 = permute(CD, PC2);
        CD = permute(CD, KS5); local KEY5 = permute(CD, PC2);
        CD = permute(CD, KS6); local KEY6 = permute(CD, PC2);
        CD = permute(CD, KS7); local KEY7 = permute(CD, PC2);
        CD = permute(CD, KS8); local KEY8 = permute(CD, PC2);
        CD = permute(CD, KS9); local KEY9 = permute(CD, PC2);
        CD = permute(CD, KS10); local KEY10 = permute(CD, PC2);
        CD = permute(CD, KS11); local KEY11 = permute(CD, PC2);
        CD = permute(CD, KS12); local KEY12 = permute(CD, PC2);
        CD = permute(CD, KS13); local KEY13 = permute(CD, PC2);
        CD = permute(CD, KS14); local KEY14 = permute(CD, PC2);
        CD = permute(CD, KS15); local KEY15 = permute(CD, PC2);
        CD = permute(CD, KS16); local KEY16 = permute(CD, PC2);

        --input permutation
        LR = permute(LR, IN_P);

        --rounds
        local frk = mix(LR, KEY1);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY2);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY3);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY4);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY5);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY6);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY7);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY8);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY9);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY10);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY11);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY12);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY13);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY14);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY15);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY16);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end

        --output permutation
        LR = permute(LR, OUT_P);

        local outputBlock = packBytes(LR);
        return outputBlock;
    end

    DES.decrypt = function(keyBlock, inputBlock)


        local LR = unpackBytes(inputBlock);
        local keyBits = unpackBytes(keyBlock);


        local CD = permute(keyBits, PC1);

        --key schedule
        CD = permute(CD, KS1); local KEY1 = permute(CD, PC2);
        CD = permute(CD, KS2); local KEY2 = permute(CD, PC2);
        CD = permute(CD, KS3); local KEY3 = permute(CD, PC2);
        CD = permute(CD, KS4); local KEY4 = permute(CD, PC2);
        CD = permute(CD, KS5); local KEY5 = permute(CD, PC2);
        CD = permute(CD, KS6); local KEY6 = permute(CD, PC2);
        CD = permute(CD, KS7); local KEY7 = permute(CD, PC2);
        CD = permute(CD, KS8); local KEY8 = permute(CD, PC2);
        CD = permute(CD, KS9); local KEY9 = permute(CD, PC2);
        CD = permute(CD, KS10); local KEY10 = permute(CD, PC2);
        CD = permute(CD, KS11); local KEY11 = permute(CD, PC2);
        CD = permute(CD, KS12); local KEY12 = permute(CD, PC2);
        CD = permute(CD, KS13); local KEY13 = permute(CD, PC2);
        CD = permute(CD, KS14); local KEY14 = permute(CD, PC2);
        CD = permute(CD, KS15); local KEY15 = permute(CD, PC2);
        CD = permute(CD, KS16); local KEY16 = permute(CD, PC2);

        --input permutation
        LR = permute(LR, IN_P);

        --rounds
        local frk = mix(LR, KEY16);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY15);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY14);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY13);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY12);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY11);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY10);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY9);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY8);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY7);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY6);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY5);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY4);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY3);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY2);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end
        LR = permute(LR, LR_SWAP);

        frk = mix(LR, KEY1);
        for k, _ in pairs(frk) do LR[k] = bxor(LR[k], frk[k]); end

        --output permutation
        LR = permute(LR, OUT_P);

        local outputBlock = packBytes(LR);
        return outputBlock;
    end

    return DES;
end

function RoCrypt.des3()

    local Array = RoCrypt.utils.array()

    local DES = RoCrypt.des()

    local DES3 = {};

    local getKeys = function(keyBlock)
        local size = Array.size(keyBlock)

        local key1;
        local key2;
        local key3;

        if (size == 8) then
            key1 = keyBlock;
            key2 = keyBlock;
            key3 = keyBlock;
        elseif (size == 16) then
            key1 = Array.slice(keyBlock, 1, 8);
            key2 = Array.slice(keyBlock, 9, 16);
            key3 = key1;
        elseif (size == 24) then
            key1 = Array.slice(keyBlock, 1, 8);
            key2 = Array.slice(keyBlock, 9, 16);
            key3 = Array.slice(keyBlock, 17, 24);
        else
            assert(false, "Invalid key size for 3DES");
        end

        return key1, key2, key3;
    end

    DES3.blockSize = DES.blockSize;

    DES3.encrypt = function(keyBlock, inputBlock)
        local key1;
        local key2;
        local key3;

        key1, key2, key3 = getKeys(keyBlock);

        local block = inputBlock;
        block = DES.encrypt(key1, block);
        block = DES.decrypt(key2, block);
        block = DES.encrypt(key3, block);

        return block;
    end

    DES3.decrypt = function(keyBlock, inputBlock)
        local key1;
        local key2;
        local key3;

        key1, key2, key3 = getKeys(keyBlock);

        local block = inputBlock;
        block = DES.decrypt(key3, block);
        block = DES.encrypt(key2, block);
        block = DES.decrypt(key1, block);

        return block;
    end

    return DES3;
end

-- @ https://gist.github.com/metatablecat/92345df2fd6d450da288c28272555faf
function RoCrypt.compression.lz4()
    local lz4 = {}

    type Streamer = {
        Offset: number,
        Source: string,
        Length: number,
        IsFinished: boolean,
        LastUnreadBytes: number,

        read: (Streamer, len: number?, shiftOffset: boolean?) -> string,
        seek: (Streamer, len: number) -> (),
        append: (Streamer, newData: string) -> (),
        toEnd: (Streamer) -> ()
    }

    type BlockData = {
        [number]: {
            Literal: string,
            LiteralLength: number,
            MatchOffset: number?,
            MatchLength: number?
        }
    }

    local function plainFind(str, pat)
        return string.find(str, pat, 0, true)
    end

    local function streamer(str): Streamer
        local Stream = {}
        Stream.Offset = 0
        Stream.Source = str
        Stream.Length = string.len(str)
        Stream.IsFinished = false	
        Stream.LastUnreadBytes = 0

        function Stream.read(self: Streamer, len: number?, shift: boolean?): string
            local len = len or 1
            local shift = if shift ~= nil then shift else true
            local dat = string.sub(self.Source, self.Offset + 1, self.Offset + len)

            local dataLength = string.len(dat)
            local unreadBytes = len - dataLength

            if shift then
                self:seek(len)
            end

            self.LastUnreadBytes = unreadBytes
            return dat
        end

        function Stream.seek(self: Streamer, len: number)
            local len = len or 1

            self.Offset = math.clamp(self.Offset + len, 0, self.Length)
            self.IsFinished = self.Offset >= self.Length
        end

        function Stream.append(self: Streamer, newData: string)
            -- adds new data to the end of a stream
            self.Source ..= newData
            self.Length = string.len(self.Source)
            self:seek(0) --hacky but forces a recalculation of the isFinished flag
        end

        function Stream.toEnd(self: Streamer)
            self:seek(self.Length)
        end

        return Stream
    end

    function lz4.compress(str: string): string
        local blocks: BlockData = {}
        local iostream = streamer(str)

        if iostream.Length > 12 then
            local firstFour = iostream:read(4)

            local processed = firstFour
            local lit = firstFour
            local match = ""
            local LiteralPushValue = ""
            local pushToLiteral = true

            repeat
                pushToLiteral = true
                local nextByte = iostream:read()

                if plainFind(processed, nextByte) then
                    local next3 = iostream:read(3, false)

                    if string.len(next3) < 3 then
                        --push bytes to literal block then break
                        LiteralPushValue = nextByte .. next3
                        iostream:seek(3)
                    else
                        match = nextByte .. next3

                        local matchPos = plainFind(processed, match)
                        if matchPos then
                            iostream:seek(3)
                            repeat
                                local nextMatchByte = iostream:read(1, false)
                                local newResult = match .. nextMatchByte

                                local repos = plainFind(processed, newResult) 
                                if repos then
                                    match = newResult
                                    matchPos = repos
                                    iostream:seek(1)
                                end
                            until not plainFind(processed, newResult) or iostream.IsFinished

                            local matchLen = string.len(match)
                            local pushMatch = true

                            if iostream.Length - iostream.Offset <= 5 then
                                LiteralPushValue = match
                                pushMatch = false
                                --better safe here, dont bother pushing to match ever
                            end

                            if pushMatch then
                                pushToLiteral = false

                                -- gets the position from the end of processed, then slaps it onto processed
                                local realPosition = string.len(processed) - matchPos
                                processed = processed .. match

                                table.insert(blocks, {
                                    Literal = lit,
                                    LiteralLength = string.len(lit),
                                    MatchOffset = realPosition + 1,
                                    MatchLength = matchLen,
                                })
                                lit = ""
                            end
                        else
                            LiteralPushValue = nextByte
                        end
                    end
                else
                    LiteralPushValue = nextByte
                end

                if pushToLiteral then
                    lit = lit .. LiteralPushValue
                    processed = processed .. nextByte
                end
            until iostream.IsFinished
            table.insert(blocks, {
                Literal = lit,
                LiteralLength = string.len(lit)
            })
        else
            local str = iostream.Source
            blocks[1] = {
                Literal = str,
                LiteralLength = string.len(str)
            }
        end

        -- generate the output chunk
        -- %s is for adding header
        local output = string.rep("\x00", 4)
        local function write(char)
            output = output .. char
        end
        -- begin working through chunks
        for chunkNum, chunk in blocks do
            local litLen = chunk.LiteralLength
            local matLen = (chunk.MatchLength or 4) - 4

            -- create token
            local tokenLit = math.clamp(litLen, 0, 15)
            local tokenMat = math.clamp(matLen, 0, 15)

            local token = bit32.lshift(tokenLit, 4) + tokenMat
            write(string.pack("<I1", token))

            if litLen >= 15 then
                litLen = litLen - 15
                --begin packing extra bytes
                repeat
                    local nextToken = math.clamp(litLen, 0, 0xFF)
                    write(string.pack("<I1", nextToken))
                    if nextToken == 0xFF then
                        litLen = litLen - 255
                    end
                until nextToken < 0xFF
            end

            -- push raw lit data
            write(chunk.Literal)

            if chunkNum ~= #blocks then
                -- push offset as u16
                write(string.pack("<I2", chunk.MatchOffset))

                -- pack extra match bytes
                if matLen >= 15 then
                    matLen = matLen - 15

                    repeat
                        local nextToken = math.clamp(matLen, 0, 0xFF)
                        write(string.pack("<I1", nextToken))
                        if nextToken == 0xFF then
                            matLen = matLen - 255
                        end
                    until nextToken < 0xFF
                end
            end
        end
        --append chunks
        local compLen = string.len(output) - 4
        local decompLen = iostream.Length
        return string.pack("<I4", compLen) .. string.pack("<I4", decompLen) .. output
    end

    function lz4.decompress(lz4data: string): string
        local inputStream = streamer(lz4data)

        local compressedLen = string.unpack("<I4", inputStream:read(4))
        local decompressedLen = string.unpack("<I4", inputStream:read(4))
        local reserved = string.unpack("<I4", inputStream:read(4))

        if compressedLen == 0 then
            return inputStream:read(decompressedLen)
        end

        local outputStream = streamer("")

        repeat
            local token = string.byte(inputStream:read())
            local litLen = bit32.rshift(token, 4)
            local matLen = bit32.band(token, 15) + 4

            if litLen >= 15 then
                repeat
                    local nextByte = string.byte(inputStream:read())
                    litLen += nextByte
                until nextByte ~= 0xFF
            end

            local literal = inputStream:read(litLen)
            outputStream:append(literal)
            outputStream:toEnd()
            if outputStream.Length < decompressedLen then
                --match
                local offset = string.unpack("<I2", inputStream:read(2))
                if matLen >= 19 then
                    repeat
                        local nextByte = string.byte(inputStream:read())
                        matLen += nextByte
                    until nextByte ~= 0xFF
                end

                outputStream:seek(-offset)
                local pos = outputStream.Offset
                local match = outputStream:read(matLen)
                local unreadBytes = outputStream.LastUnreadBytes
                local extra
                if unreadBytes then
                    repeat
                        outputStream.Offset = pos
                        extra = outputStream:read(unreadBytes)
                        unreadBytes = outputStream.LastUnreadBytes
                        match ..= extra
                    until unreadBytes <= 0
                end

                outputStream:append(match)
                outputStream:toEnd()
            end

        until outputStream.Length >= decompressedLen

        return outputStream.Source
    end

    return lz4
end


-- @ https://github.com/SafeteeWoW/LibDeflate/
local function libdeflate_bootstrapper()
    local LibDeflate

    do
        -- Semantic version. all lowercase.
        -- Suffix can be alpha1, alpha2, beta1, beta2, rc1, rc2, etc.
        -- NOTE: Two version numbers needs to modify.
        -- 1. On the top of LibDeflate.lua
        -- 2. _VERSION
        -- 3. _MINOR

        -- version to store the official version of LibDeflate
        local _VERSION = "1.0.2-release"

        -- When MAJOR is changed, I should name it as LibDeflate2
        local _MAJOR = "LibDeflate"

        -- Update this whenever a new version, for LibStub version registration.
        -- 0 : v0.x
        -- 1 : v1.0.0
        -- 2 : v1.0.1
        -- 3 : v1.0.2
        local _MINOR = 3

        local _COPYRIGHT = "LibDeflate " .. _VERSION ..
            " Copyright (C) 2018-2021 Haoqian He." ..
            " Licensed under the zlib License"

        -- Register in the World of Warcraft library "LibStub" if detected.

        LibDeflate = {}
    end


    -- Converts i to 2^i, (0<=i<=32)
    -- This is used to implement bit left shift and bit right shift.
    -- "x >> y" in C:   "(x-x%_pow2[y])/_pow2[y]" in Lua
    -- "x << y" in C:   "x*_pow2[y]" in Lua
    local _pow2 = {}

    -- Converts any byte to a character, (0<=byte<=255)
    local _byte_to_char = {}

    -- _reverseBitsTbl[len][val] stores the bit reverse of
    -- the number with bit length "len" and value "val"
    -- For example, decimal number 6 with bits length 5 is binary 00110
    -- It's reverse is binary 01100,
    -- which is decimal 12 and 12 == _reverseBitsTbl[5][6]
    -- 1<=len<=9, 0<=val<=2^len-1
    -- The reason for 1<=len<=9 is that the max of min bitlen of huffman code
    -- of a huffman alphabet is 9?
    local _reverse_bits_tbl = {}

    -- Convert a LZ77 length (3<=len<=258) to
    -- a deflate literal/LZ77_length code (257<=code<=285)
    local _length_to_deflate_code = {}

    -- convert a LZ77 length (3<=len<=258) to
    -- a deflate literal/LZ77_length code extra bits.
    local _length_to_deflate_extra_bits = {}

    -- Convert a LZ77 length (3<=len<=258) to
    -- a deflate literal/LZ77_length code extra bit length.
    local _length_to_deflate_extra_bitlen = {}

    -- Convert a small LZ77 distance (1<=dist<=256) to a deflate code.
    local _dist256_to_deflate_code = {}

    -- Convert a small LZ77 distance (1<=dist<=256) to
    -- a deflate distance code extra bits.
    local _dist256_to_deflate_extra_bits = {}

    -- Convert a small LZ77 distance (1<=dist<=256) to
    -- a deflate distance code extra bit length.
    local _dist256_to_deflate_extra_bitlen = {}

    -- Convert a literal/LZ77_length deflate code to LZ77 base length
    -- The key of the table is (code - 256), 257<=code<=285
    local _literal_deflate_code_to_base_len =
        {
            3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67,
            83, 99, 115, 131, 163, 195, 227, 258
        }

    -- Convert a literal/LZ77_length deflate code to base LZ77 length extra bits
    -- The key of the table is (code - 256), 257<=code<=285
    local _literal_deflate_code_to_extra_bitlen =
        {
            0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5,
            5, 5, 5, 0
        }

    -- Convert a distance deflate code to base LZ77 distance. (0<=code<=29)
    local _dist_deflate_code_to_base_dist = {
        [0] = 1,
        2,
        3,
        4,
        5,
        7,
        9,
        13,
        17,
        25,
        33,
        49,
        65,
        97,
        129,
        193,
        257,
        385,
        513,
        769,
        1025,
        1537,
        2049,
        3073,
        4097,
        6145,
        8193,
        12289,
        16385,
        24577
    }

    -- Convert a distance deflate code to LZ77 bits length. (0<=code<=29)
    local _dist_deflate_code_to_extra_bitlen =
        {
            [0] = 0,
            0,
            0,
            0,
            1,
            1,
            2,
            2,
            3,
            3,
            4,
            4,
            5,
            5,
            6,
            6,
            7,
            7,
            8,
            8,
            9,
            9,
            10,
            10,
            11,
            11,
            12,
            12,
            13,
            13
        }

    -- The code order of the first huffman header in the dynamic deflate block.
    -- See the page 12 of RFC1951
    local _rle_codes_huffman_bitlen_order = {
        16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
    }

    -- The following tables are used by fixed deflate block.
    -- The value of these tables are assigned at the bottom of the source.

    -- The huffman code of the literal/LZ77_length deflate codes,
    -- in fixed deflate block.
    local _fix_block_literal_huffman_code

    -- Convert huffman code of the literal/LZ77_length to deflate codes,
    -- in fixed deflate block.
    local _fix_block_literal_huffman_to_deflate_code

    -- The bit length of the huffman code of literal/LZ77_length deflate codes,
    -- in fixed deflate block.
    local _fix_block_literal_huffman_bitlen

    -- The count of each bit length of the literal/LZ77_length deflate codes,
    -- in fixed deflate block.
    local _fix_block_literal_huffman_bitlen_count

    -- The huffman code of the distance deflate codes,
    -- in fixed deflate block.
    local _fix_block_dist_huffman_code

    -- Convert huffman code of the distance to deflate codes,
    -- in fixed deflate block.
    local _fix_block_dist_huffman_to_deflate_code

    -- The bit length of the huffman code of the distance deflate codes,
    -- in fixed deflate block.
    local _fix_block_dist_huffman_bitlen

    -- The count of each bit length of the huffman code of
    -- the distance deflate codes,
    -- in fixed deflate block.
    local _fix_block_dist_huffman_bitlen_count

    for i = 0, 255 do _byte_to_char[i] = string.char(i) end

    do
        local pow = 1
        for i = 0, 32 do
            _pow2[i] = pow
            pow = pow * 2
        end
    end

    for i = 1, 9 do
        _reverse_bits_tbl[i] = {}
        for j = 0, _pow2[i + 1] - 1 do
            local reverse = 0
            local value = j
            for _ = 1, i do
                -- The following line is equivalent to "res | (code %2)" in C.
                reverse = reverse - reverse % 2 +
                    (((reverse % 2 == 1) or (value % 2) == 1) and 1 or 0)
                value = (value - value % 2) / 2
                reverse = reverse * 2
            end
            _reverse_bits_tbl[i][j] = (reverse - reverse % 2) / 2
        end
    end

    -- The source code is written according to the pattern in the numbers
    -- in RFC1951 Page10.
    do
        local a = 18
        local b = 16
        local c = 265
        local bitlen = 1
        for len = 3, 258 do
            if len <= 10 then
                _length_to_deflate_code[len] = len + 254
                _length_to_deflate_extra_bitlen[len] = 0
            elseif len == 258 then
                _length_to_deflate_code[len] = 285
                _length_to_deflate_extra_bitlen[len] = 0
            else
                if len > a then
                    a = a + b
                    b = b * 2
                    c = c + 4
                    bitlen = bitlen + 1
                end
                local t = len - a - 1 + b / 2
                _length_to_deflate_code[len] = (t - (t % (b / 8))) / (b / 8) + c
                _length_to_deflate_extra_bitlen[len] = bitlen
                _length_to_deflate_extra_bits[len] = t % (b / 8)
            end
        end
    end

    -- The source code is written according to the pattern in the numbers
    -- in RFC1951 Page11.
    do
        _dist256_to_deflate_code[1] = 0
        _dist256_to_deflate_code[2] = 1
        _dist256_to_deflate_extra_bitlen[1] = 0
        _dist256_to_deflate_extra_bitlen[2] = 0

        local a = 3
        local b = 4
        local code = 2
        local bitlen = 0
        for dist = 3, 256 do
            if dist > b then
                a = a * 2
                b = b * 2
                code = code + 2
                bitlen = bitlen + 1
            end
            _dist256_to_deflate_code[dist] = (dist <= a) and code or (code + 1)
            _dist256_to_deflate_extra_bitlen[dist] = (bitlen < 0) and 0 or bitlen
            if b >= 8 then
                _dist256_to_deflate_extra_bits[dist] = (dist - b / 2 - 1) % (b / 4)
            end
        end
    end

    --- Calculate the Adler-32 checksum of the string. <br>
    -- See RFC1950 Page 9 https://tools.ietf.org/html/rfc1950 for the
    -- definition of Adler-32 checksum.
    -- @param str [string] the input string to calcuate its Adler-32 checksum.
    -- @return [integer] The Adler-32 checksum, which is greater or equal to 0,
    -- and less than 2^32 (4294967296).
    function LibDeflate:Adler32(str)
        -- This function is loop unrolled by better performance.
        --
        -- Here is the minimum code:
        --
        -- local a = 1
        -- local b = 0
        -- for i=1, #str do
        -- 		local s = string.byte(str, i, i)
        -- 		a = (a+s)%65521
        -- 		b = (b+a)%65521
        -- 		end
        -- return b*65536+a
        if type(str) ~= "string" then
            error(("Usage: LibDeflate:Adler32(str):" ..
                " 'str' - string expected got '%s'."):format(type(str)), 2)
        end
        local strlen = #str

        local i = 1
        local a = 1
        local b = 0
        while i <= strlen - 15 do
            local x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16 =
                string.byte(str, i, i + 15)
            b =
                (b + 16 * a + 16 * x1 + 15 * x2 + 14 * x3 + 13 * x4 + 12 * x5 + 11 * x6 +
                    10 * x7 + 9 * x8 + 8 * x9 + 7 * x10 + 6 * x11 + 5 * x12 + 4 * x13 + 3 *
                    x14 + 2 * x15 + x16) % 65521
            a =
                (a + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 +
                    x14 + x15 + x16) % 65521
            i = i + 16
        end
        while (i <= strlen) do
            local x = string.byte(str, i, i)
            a = (a + x) % 65521
            b = (b + a) % 65521
            i = i + 1
        end
        return (b * 65536 + a) % 4294967296
    end

    -- Compare adler32 checksum.
    -- adler32 should be compared with a mod to avoid sign problem
    -- 4072834167 (unsigned) is the same adler32 as -222133129
    local function IsEqualAdler32(actual, expected)
        return (actual % 4294967296) == (expected % 4294967296)
    end


    -- Check if the dictionary is valid.
    -- @param dictionary The preset dictionary for compression and decompression.
    -- @return true if valid, false if not valid.
    -- @return if not valid, the error message.


--[[
	key of the configuration table is the compression level,
	and its value stores the compression setting.
	These numbers come from zlib source code.

	Higher compression level usually means better compression.
	(Because LibDeflate uses a simplified version of zlib algorithm,
	there is no guarantee that higher compression level does not create
	bigger file than lower level, but I can say it's 99% likely)

	Be careful with the high compression level. This is a pure lua
	implementation compressor/decompressor, which is significant slower than
	a C/C++ equivalant compressor/decompressor. Very high compression level
	costs significant more CPU time, and usually compression size won't be
	significant smaller when you increase compression level by 1, when the
	level is already very high. Benchmark yourself if you can afford it.

	See also https://github.com/madler/zlib/blob/master/doc/algorithm.txt,
	https://github.com/madler/zlib/blob/master/deflate.c for more information.

	The meaning of each field:
	@field 1 use_lazy_evaluation:
		true/false. Whether the program uses lazy evaluation.
		See what is "lazy evaluation" in the link above.
		lazy_evaluation improves ratio, but relatively slow.
	@field 2 good_prev_length:
		Only effective if lazy is set, Only use 1/4 of max_chain,
		if prev length of lazy match is above this.
	@field 3 max_insert_length/max_lazy_match:
		If not using lazy evaluation,
		insert new strings in the hash table only if the match length is not
		greater than this length.
		If using lazy evaluation, only continue lazy evaluation,
		if previous match length is strictly smaller than this value.
	@field 4 nice_length:
		Number. Don't continue to go down the hash chain,
		if match length is above this.
	@field 5 max_chain:
		Number. The maximum number of hash chains we look.
--]]
    local _compression_level_configs = {
        [0] = {false, nil, 0, 0, 0}, -- level 0, no compression
        [1] = {false, nil, 4, 8, 4}, -- level 1, similar to zlib level 1
        [2] = {false, nil, 5, 18, 8}, -- level 2, similar to zlib level 2
        [3] = {false, nil, 6, 32, 32}, -- level 3, similar to zlib level 3
        [4] = {true, 4, 4, 16, 16}, -- level 4, similar to zlib level 4
        [5] = {true, 8, 16, 32, 32}, -- level 5, similar to zlib level 5
        [6] = {true, 8, 16, 128, 128}, -- level 6, similar to zlib level 6
        [7] = {true, 8, 32, 128, 256}, -- (SLOW) level 7, similar to zlib level 7
        [8] = {true, 32, 128, 258, 1024}, -- (SLOW) level 8,similar to zlib level 8
        [9] = {true, 32, 258, 258, 4096}
        -- (VERY SLOW) level 9, similar to zlib level 9
    }

    -- Check if the compression/decompression arguments is valid
    -- @param str The input string.
    -- @param check_dictionary if true, check if dictionary is valid.
    -- @param dictionary The preset dictionary for compression and decompression.
    -- @param check_configs if true, check if config is valid.
    -- @param configs The compression configuration table
    -- @return true if valid, false if not valid.
    -- @return if not valid, the error message.
    local function IsValidArguments(str, check_dictionary, dictionary,
        check_configs, configs)

        if type(str) ~= "string" then
            return false, ("'str' - string expected got '%s'."):format(type(str))
        end
        if check_configs then
            local type_configs = type(configs)
            if type_configs ~= "nil" and type_configs ~= "table" then
                return false, ("'configs' - nil or table expected got '%s'."):format(
                type(configs))
            end
            if type_configs == "table" then
                for k, v in pairs(configs) do
                    if k ~= "level" and k ~= "strategy" then
                        return false,
                        ("'configs' - unsupported table key in the configs: '%s'."):format(
                        k)
                    elseif k == "level" and not _compression_level_configs[v] then
                        return false,
                        ("'configs' - unsupported 'level': %s."):format(tostring(v))
                    elseif k == "strategy" and v ~= "fixed" and v ~= "huffman_only" and v ~=
                        "dynamic" then
                        -- random_block_type is for testing purpose
                        return false, ("'configs' - unsupported 'strategy': '%s'."):format(
                        tostring(v))
                    end
                end
            end
        end
        return true, ""
    end

--[[ --------------------------------------------------------------------------
	Compress code
--]] --------------------------------------------------------------------------

    -- partial flush to save memory
    local _FLUSH_MODE_MEMORY_CLEANUP = 0
    -- full flush with partial bytes
    local _FLUSH_MODE_OUTPUT = 1
    -- write bytes to get to byte boundary
    local _FLUSH_MODE_BYTE_BOUNDARY = 2
    -- no flush, just get num of bits written so far
    local _FLUSH_MODE_NO_FLUSH = 3

--[[
	Create an empty writer to easily write stuffs as the unit of bits.
	Return values:
	1. WriteBits(code, bitlen):
	2. WriteString(str):
	3. Flush(mode):
--]]
    local function CreateWriter()
        local buffer_size = 0
        local cache = 0
        local cache_bitlen = 0
        local total_bitlen = 0
        local buffer = {}
        -- When buffer is big enough, flush into result_buffer to save memory.
        local result_buffer = {}

        -- Write bits with value "value" and bit length of "bitlen" into writer.
        -- @param value: The value being written
        -- @param bitlen: The bit length of "value"
        -- @return nil
        local function WriteBits(value, bitlen)
            cache = cache + value * _pow2[cache_bitlen]
            cache_bitlen = cache_bitlen + bitlen
            total_bitlen = total_bitlen + bitlen
            -- Only bulk to buffer every 4 bytes. This is quicker.
            if cache_bitlen >= 32 then
                buffer_size = buffer_size + 1
                buffer[buffer_size] = _byte_to_char[cache % 256] ..
                    _byte_to_char[((cache - cache % 256) / 256 % 256)] ..
                    _byte_to_char[((cache - cache % 65536) / 65536 %
                        256)] ..
                    _byte_to_char[((cache - cache % 16777216) /
                        16777216 % 256)]
                local rshift_mask = _pow2[32 - cache_bitlen + bitlen]
                cache = (value - value % rshift_mask) / rshift_mask
                cache_bitlen = cache_bitlen - 32
            end
        end

        -- Write the entire string into the writer.
        -- @param str The string being written
        -- @return nil
        local function WriteString(str)
            for _ = 1, cache_bitlen, 8 do
                buffer_size = buffer_size + 1
                buffer[buffer_size] = string.char(cache % 256)
                cache = (cache - cache % 256) / 256
            end
            cache_bitlen = 0
            buffer_size = buffer_size + 1
            buffer[buffer_size] = str
            total_bitlen = total_bitlen + #str * 8
        end

        -- Flush current stuffs in the writer and return it.
        -- This operation will free most of the memory.
        -- @param mode See the descrtion of the constant and the source code.
        -- @return The total number of bits stored in the writer right now.
        -- for byte boundary mode, it includes the padding bits.
        -- for output mode, it does not include padding bits.
        -- @return Return the outputs if mode is output.
        local function FlushWriter(mode)
            if mode == _FLUSH_MODE_NO_FLUSH then return total_bitlen end

            if mode == _FLUSH_MODE_OUTPUT or mode == _FLUSH_MODE_BYTE_BOUNDARY then
                -- Full flush, also output cache.
                -- Need to pad some bits if cache_bitlen is not multiple of 8.
                local padding_bitlen = (8 - cache_bitlen % 8) % 8

                if cache_bitlen > 0 then
                    -- padding with all 1 bits, mainly because "\000" is not
                    -- good to be tranmitted. I do this so "\000" is a little bit
                    -- less frequent.
                    cache = cache - _pow2[cache_bitlen] +
                        _pow2[cache_bitlen + padding_bitlen]
                    for _ = 1, cache_bitlen, 8 do
                        buffer_size = buffer_size + 1
                        buffer[buffer_size] = _byte_to_char[cache % 256]
                        cache = (cache - cache % 256) / 256
                    end

                    cache = 0
                    cache_bitlen = 0
                end
                if mode == _FLUSH_MODE_BYTE_BOUNDARY then
                    total_bitlen = total_bitlen + padding_bitlen
                    return total_bitlen
                end
            end

            local flushed = table.concat(buffer)
            buffer = {}
            buffer_size = 0
            result_buffer[#result_buffer + 1] = flushed

            if mode == _FLUSH_MODE_MEMORY_CLEANUP then
                return total_bitlen
            else
                return total_bitlen, table.concat(result_buffer)
            end
        end

        return WriteBits, WriteString, FlushWriter
    end

    -- Push an element into a max heap
    -- @param heap A max heap whose max element is at index 1.
    -- @param e The element to be pushed. Assume element "e" is a table
    --  and comparison is done via its first entry e[1]
    -- @param heap_size current number of elements in the heap.
    --  NOTE: There may be some garbage stored in
    --  heap[heap_size+1], heap[heap_size+2], etc..
    -- @return nil
    local function MinHeapPush(heap, e, heap_size)
        heap_size = heap_size + 1
        heap[heap_size] = e
        local value = e[1]
        local pos = heap_size
        local parent_pos = (pos - pos % 2) / 2

        while (parent_pos >= 1 and heap[parent_pos][1] > value) do
            local t = heap[parent_pos]
            heap[parent_pos] = e
            heap[pos] = t
            pos = parent_pos
            parent_pos = (parent_pos - parent_pos % 2) / 2
        end
    end

    -- Pop an element from a max heap
    -- @param heap A max heap whose max element is at index 1.
    -- @param heap_size current number of elements in the heap.
    -- @return the poped element
    -- Note: This function does not change table size of "heap" to save CPU time.
    local function MinHeapPop(heap, heap_size)
        local top = heap[1]
        local e = heap[heap_size]
        local value = e[1]
        heap[1] = e
        heap[heap_size] = top
        heap_size = heap_size - 1

        local pos = 1
        local left_child_pos = pos * 2
        local right_child_pos = left_child_pos + 1

        while (left_child_pos <= heap_size) do
            local left_child = heap[left_child_pos]
            if (right_child_pos <= heap_size and heap[right_child_pos][1] <
                left_child[1]) then
                local right_child = heap[right_child_pos]
                if right_child[1] < value then
                    heap[right_child_pos] = e
                    heap[pos] = right_child
                    pos = right_child_pos
                    left_child_pos = pos * 2
                    right_child_pos = left_child_pos + 1
                else
                    break
                end
            else
                if left_child[1] < value then
                    heap[left_child_pos] = e
                    heap[pos] = left_child
                    pos = left_child_pos
                    left_child_pos = pos * 2
                    right_child_pos = left_child_pos + 1
                else
                    break
                end
            end
        end

        return top
    end

    -- Deflate defines a special huffman tree, which is unique once the bit length
    -- of huffman code of all symbols are known.
    -- @param bitlen_count Number of symbols with a specific bitlen
    -- @param symbol_bitlen The bit length of a symbol
    -- @param max_symbol The max symbol among all symbols,
    --		which is (number of symbols - 1)
    -- @param max_bitlen The max huffman bit length among all symbols.
    -- @return The huffman code of all symbols.
    local function GetHuffmanCodeFromBitlen(bitlen_counts, symbol_bitlens,
        max_symbol, max_bitlen)
        local huffman_code = 0
        local next_codes = {}
        local symbol_huffman_codes = {}
        for bitlen = 1, max_bitlen do
            huffman_code = (huffman_code + (bitlen_counts[bitlen - 1] or 0)) * 2
            next_codes[bitlen] = huffman_code
        end
        for symbol = 0, max_symbol do
            local bitlen = symbol_bitlens[symbol]
            if bitlen then
                huffman_code = next_codes[bitlen]
                next_codes[bitlen] = huffman_code + 1

                -- Reverse the bits of huffman code,
                -- because most signifant bits of huffman code
                -- is stored first into the compressed data.
                -- @see RFC1951 Page5 Section 3.1.1
                if bitlen <= 9 then -- Have cached reverse for small bitlen.
                    symbol_huffman_codes[symbol] = _reverse_bits_tbl[bitlen][huffman_code]
                else
                    local reverse = 0
                    for _ = 1, bitlen do
                        reverse = reverse - reverse % 2 +
                            (((reverse % 2 == 1) or (huffman_code % 2) == 1) and 1 or
                                0)
                        huffman_code = (huffman_code - huffman_code % 2) / 2
                        reverse = reverse * 2
                    end
                    symbol_huffman_codes[symbol] = (reverse - reverse % 2) / 2
                end
            end
        end
        return symbol_huffman_codes
    end

    -- A helper function to sort heap elements
    -- a[1], b[1] is the huffman frequency
    -- a[2], b[2] is the symbol value.
    local function SortByFirstThenSecond(a, b)
        return a[1] < b[1] or (a[1] == b[1] and a[2] < b[2])
    end

    -- Calculate the huffman bit length and huffman code.
    -- @param symbol_count: A table whose table key is the symbol, and table value
    --		is the symbol frenquency (nil means 0 frequency).
    -- @param max_bitlen: See description of return value.
    -- @param max_symbol: The maximum symbol
    -- @return a table whose key is the symbol, and the value is the huffman bit
    --		bit length. We guarantee that all bit length <= max_bitlen.
    --		For 0<=symbol<=max_symbol, table value could be nil if the frequency
    --		of the symbol is 0 or nil.
    -- @return a table whose key is the symbol, and the value is the huffman code.
    -- @return a number indicating the maximum symbol whose bitlen is not 0.
    local function GetHuffmanBitlenAndCode(symbol_counts, max_bitlen, max_symbol)
        local heap_size
        local max_non_zero_bitlen_symbol = -1
        local leafs = {}
        local heap = {}
        local symbol_bitlens = {}
        local symbol_codes = {}
        local bitlen_counts = {}

  --[[
		tree[1]: weight, temporarily used as parent and bitLengths
		tree[2]: symbol
		tree[3]: left child
		tree[4]: right child
	--]]
        local number_unique_symbols = 0
        for symbol, count in pairs(symbol_counts) do
            number_unique_symbols = number_unique_symbols + 1
            leafs[number_unique_symbols] = {count, symbol}
        end

        if (number_unique_symbols == 0) then
            -- no code.
            return {}, {}, -1
        elseif (number_unique_symbols == 1) then
            -- Only one code. In this case, its huffman code
            -- needs to be assigned as 0, and bit length is 1.
            -- This is the only case that the return result
            -- represents an imcomplete huffman tree.
            local symbol = leafs[1][2]
            symbol_bitlens[symbol] = 1
            symbol_codes[symbol] = 0
            return symbol_bitlens, symbol_codes, symbol
        else
            table.sort(leafs, SortByFirstThenSecond)
            heap_size = number_unique_symbols
            for i = 1, heap_size do heap[i] = leafs[i] end

            while (heap_size > 1) do
                -- Note: pop does not change table size of heap
                local leftChild = MinHeapPop(heap, heap_size)
                heap_size = heap_size - 1
                local rightChild = MinHeapPop(heap, heap_size)
                heap_size = heap_size - 1
                local newNode = {leftChild[1] + rightChild[1], -1, leftChild, rightChild}
                MinHeapPush(heap, newNode, heap_size)
                heap_size = heap_size + 1
            end

            -- Number of leafs whose bit length is greater than max_len.
            local number_bitlen_overflow = 0

            -- Calculate bit length of all nodes
            local fifo = {heap[1], 0, 0, 0} -- preallocate some spaces.
            local fifo_size = 1
            local index = 1
            heap[1][1] = 0
            while (index <= fifo_size) do -- Breath first search
                local e = fifo[index]
                local bitlen = e[1]
                local symbol = e[2]
                local left_child = e[3]
                local right_child = e[4]
                if left_child then
                    fifo_size = fifo_size + 1
                    fifo[fifo_size] = left_child
                    left_child[1] = bitlen + 1
                end
                if right_child then
                    fifo_size = fifo_size + 1
                    fifo[fifo_size] = right_child
                    right_child[1] = bitlen + 1
                end
                index = index + 1

                if (bitlen > max_bitlen) then
                    number_bitlen_overflow = number_bitlen_overflow + 1
                    bitlen = max_bitlen
                end
                if symbol >= 0 then
                    symbol_bitlens[symbol] = bitlen
                    max_non_zero_bitlen_symbol = (symbol > max_non_zero_bitlen_symbol) and
                        symbol or max_non_zero_bitlen_symbol
                    bitlen_counts[bitlen] = (bitlen_counts[bitlen] or 0) + 1
                end
            end

            -- Resolve bit length overflow
            -- @see ZLib/trees.c:gen_bitlen(s, desc), for reference
            if (number_bitlen_overflow > 0) then
                repeat
                    local bitlen = max_bitlen - 1
                    while ((bitlen_counts[bitlen] or 0) == 0) do bitlen = bitlen - 1 end
                    -- move one leaf down the tree
                    bitlen_counts[bitlen] = bitlen_counts[bitlen] - 1
                    -- move one overflow item as its brother
                    bitlen_counts[bitlen + 1] = (bitlen_counts[bitlen + 1] or 0) + 2
                    bitlen_counts[max_bitlen] = bitlen_counts[max_bitlen] - 1
                    number_bitlen_overflow = number_bitlen_overflow - 2
                until (number_bitlen_overflow <= 0)

                index = 1
                for bitlen = max_bitlen, 1, -1 do
                    local n = bitlen_counts[bitlen] or 0
                    while (n > 0) do
                        local symbol = leafs[index][2]
                        symbol_bitlens[symbol] = bitlen
                        n = n - 1
                        index = index + 1
                    end
                end
            end

            symbol_codes = GetHuffmanCodeFromBitlen(bitlen_counts, symbol_bitlens,
                max_symbol, max_bitlen)
            return symbol_bitlens, symbol_codes, max_non_zero_bitlen_symbol
        end
    end

    -- Calculate the first huffman header in the dynamic huffman block
    -- @see RFC1951 Page 12
    -- @param lcode_bitlen: The huffman bit length of literal/LZ77_length.
    -- @param max_non_zero_bitlen_lcode: The maximum literal/LZ77_length symbol
    --		whose huffman bit length is not zero.
    -- @param dcode_bitlen: The huffman bit length of LZ77 distance.
    -- @param max_non_zero_bitlen_dcode: The maximum LZ77 distance symbol
    --		whose huffman bit length is not zero.
    -- @return The run length encoded codes.
    -- @return The extra bits. One entry for each rle code that needs extra bits.
    --		(code == 16 or 17 or 18).
    -- @return The count of appearance of each rle codes.
    local function RunLengthEncodeHuffmanBitlen(lcode_bitlens,
        max_non_zero_bitlen_lcode,
        dcode_bitlens,
        max_non_zero_bitlen_dcode)
        local rle_code_tblsize = 0
        local rle_codes = {}
        local rle_code_counts = {}
        local rle_extra_bits_tblsize = 0
        local rle_extra_bits = {}
        local prev = nil
        local count = 0

        -- If there is no distance code, assume one distance code of bit length 0.
        -- RFC1951: One distance code of zero bits means that
        -- there are no distance codes used at all (the data is all literals).
        max_non_zero_bitlen_dcode = (max_non_zero_bitlen_dcode < 0) and 0 or
            max_non_zero_bitlen_dcode
        local max_code = max_non_zero_bitlen_lcode + max_non_zero_bitlen_dcode + 1

        for code = 0, max_code + 1 do
            local len = (code <= max_non_zero_bitlen_lcode) and
                (lcode_bitlens[code] or 0) or ((code <= max_code) and
                (dcode_bitlens[code - max_non_zero_bitlen_lcode - 1] or 0) or
                nil)
            if len == prev then
                count = count + 1
                if len ~= 0 and count == 6 then
                    rle_code_tblsize = rle_code_tblsize + 1
                    rle_codes[rle_code_tblsize] = 16
                    rle_extra_bits_tblsize = rle_extra_bits_tblsize + 1
                    rle_extra_bits[rle_extra_bits_tblsize] = 3
                    rle_code_counts[16] = (rle_code_counts[16] or 0) + 1
                    count = 0
                elseif len == 0 and count == 138 then
                    rle_code_tblsize = rle_code_tblsize + 1
                    rle_codes[rle_code_tblsize] = 18
                    rle_extra_bits_tblsize = rle_extra_bits_tblsize + 1
                    rle_extra_bits[rle_extra_bits_tblsize] = 127
                    rle_code_counts[18] = (rle_code_counts[18] or 0) + 1
                    count = 0
                end
            else
                if count == 1 then
                    rle_code_tblsize = rle_code_tblsize + 1
                    rle_codes[rle_code_tblsize] = prev
                    rle_code_counts[prev] = (rle_code_counts[prev] or 0) + 1
                elseif count == 2 then
                    rle_code_tblsize = rle_code_tblsize + 1
                    rle_codes[rle_code_tblsize] = prev
                    rle_code_tblsize = rle_code_tblsize + 1
                    rle_codes[rle_code_tblsize] = prev
                    rle_code_counts[prev] = (rle_code_counts[prev] or 0) + 2
                elseif count >= 3 then
                    rle_code_tblsize = rle_code_tblsize + 1
                    local rleCode = (prev ~= 0) and 16 or (count <= 10 and 17 or 18)
                    rle_codes[rle_code_tblsize] = rleCode
                    rle_code_counts[rleCode] = (rle_code_counts[rleCode] or 0) + 1
                    rle_extra_bits_tblsize = rle_extra_bits_tblsize + 1
                    rle_extra_bits[rle_extra_bits_tblsize] =
                        (count <= 10) and (count - 3) or (count - 11)
                end

                prev = len
                if len and len ~= 0 then
                    rle_code_tblsize = rle_code_tblsize + 1
                    rle_codes[rle_code_tblsize] = len
                    rle_code_counts[len] = (rle_code_counts[len] or 0) + 1
                    count = 0
                else
                    count = 1
                end
            end
        end

        return rle_codes, rle_extra_bits, rle_code_counts
    end

    -- Load the string into a table, in order to speed up LZ77.
    -- Loop unrolled 16 times to speed this function up.
    -- @param str The string to be loaded.
    -- @param t The load destination
    -- @param start str[index] will be the first character to be loaded.
    -- @param end str[index] will be the last character to be loaded
    -- @param offset str[index] will be loaded into t[index-offset]
    -- @return t
    local function LoadStringToTable(str, t, start, stop, offset)
        local i = start - offset
        while i <= stop - 15 - offset do
            t[i], t[i + 1], t[i + 2], t[i + 3], t[i + 4], t[i + 5], t[i + 6], t[i + 7], t[i +
                8], t[i + 9], t[i + 10], t[i + 11], t[i + 12], t[i + 13], t[i + 14], t[i +
                15] = string.byte(str, i + offset, i + 15 + offset)
            i = i + 16
        end
        while (i <= stop - offset) do
            t[i] = string.byte(str, i + offset, i + offset)
            i = i + 1
        end
        return t
    end

    -- Do LZ77 process. This function uses the majority of the CPU time.
    -- @see zlib/deflate.c:deflate_fast(), zlib/deflate.c:deflate_slow()
    -- @see https://github.com/madler/zlib/blob/master/doc/algorithm.txt
    -- This function uses the algorithms used above. You should read the
    -- algorithm.txt above to understand what is the hash function and the
    -- lazy evaluation.
    --
    -- The special optimization used here is hash functions used here.
    -- The hash function is just the multiplication of the three consective
    -- characters. So if the hash matches, it guarantees 3 characters are matched.
    -- This optimization can be implemented because Lua table is a hash table.
    --
    -- @param level integer that describes compression level.
    -- @param string_table table that stores the value of string to be compressed.
    --			The index of this table starts from 1.
    --			The caller needs to make sure all values needed by this function
    --			are loaded.
    --			Assume "str" is the origin input string into the compressor
    --			str[block_start]..str[block_end+3] needs to be loaded into
    --			string_table[block_start-offset]..string_table[block_end-offset]
    --			If dictionary is presented, the last 258 bytes of the dictionary
    --			needs to be loaded into sing_table[-257..0]
    --			(See more in the description of offset.)
    -- @param hash_tables. The table key is the hash value (0<=hash<=16777216=256^3)
    --			The table value is an array0 that stores the indexes of the
    --			input data string to be compressed, such that
    --			hash == str[index]*str[index+1]*str[index+2]
    --			Indexes are ordered in this array.
    -- @param block_start The indexes of the input data string to be compressed.
    --				that starts the LZ77 block.
    -- @param block_end The indexes of the input data string to be compressed.
    --				that stores the LZ77 block.
    -- @param offset str[index] is stored in string_table[index-offset],
    --			This offset is mainly an optimization to limit the index
    --			of string_table, so lua can access this table quicker.
    -- @param dictionary See LibDeflate:CreateDictionary
    -- @return literal/LZ77_length deflate codes.
    -- @return the extra bits of literal/LZ77_length deflate codes.
    -- @return the count of each literal/LZ77 deflate code.
    -- @return LZ77 distance deflate codes.
    -- @return the extra bits of LZ77 distance deflate codes.
    -- @return the count of each LZ77 distance deflate code.
    local function GetBlockLZ77Result(level, string_table, hash_tables, block_start,
        block_end, offset, dictionary)
        local config = _compression_level_configs[level]
        local config_use_lazy, config_good_prev_length, config_max_lazy_match,
        config_nice_length, config_max_hash_chain = config[1], config[2],
        config[3], config[4],
        config[5]

        local config_max_insert_length = (not config_use_lazy) and
            config_max_lazy_match or 2147483646
        local config_good_hash_chain =
            (config_max_hash_chain - config_max_hash_chain % 4 / 4)

        local hash

        local dict_hash_tables
        local dict_string_table
        local dict_string_len = 0

        if dictionary then
            dict_hash_tables = dictionary.hash_tables
            dict_string_table = dictionary.string_table
            dict_string_len = dictionary.strlen
            assert(block_start == 1)
            if block_end >= block_start and dict_string_len >= 2 then
                hash = dict_string_table[dict_string_len - 1] * 65536 +
                    dict_string_table[dict_string_len] * 256 + string_table[1]
                local t = hash_tables[hash]
                if not t then
                    t = {};
                    hash_tables[hash] = t
                end
                t[#t + 1] = -1
            end
            if block_end >= block_start + 1 and dict_string_len >= 1 then
                hash =
                    dict_string_table[dict_string_len] * 65536 + string_table[1] * 256 +
                    string_table[2]
                local t = hash_tables[hash]
                if not t then
                    t = {};
                    hash_tables[hash] = t
                end
                t[#t + 1] = 0
            end
        end

        local dict_string_len_plus3 = dict_string_len + 3

        hash = (string_table[block_start - offset] or 0) * 256 +
            (string_table[block_start + 1 - offset] or 0)

        local lcodes = {}
        local lcode_tblsize = 0
        local lcodes_counts = {}
        local dcodes = {}
        local dcodes_tblsize = 0
        local dcodes_counts = {}

        local lextra_bits = {}
        local lextra_bits_tblsize = 0
        local dextra_bits = {}
        local dextra_bits_tblsize = 0

        local match_available = false
        local prev_len
        local prev_dist
        local cur_len = 0
        local cur_dist = 0

        local index = block_start
        local index_end = block_end + (config_use_lazy and 1 or 0)

        -- the zlib source code writes separate code for lazy evaluation and
        -- not lazy evaluation, which is easier to understand.
        -- I put them together, so it is a bit harder to understand.
        -- because I think this is easier for me to maintain it.
        while (index <= index_end) do
            local string_table_index = index - offset
            local offset_minus_three = offset - 3
            prev_len = cur_len
            prev_dist = cur_dist
            cur_len = 0

            hash = (hash * 256 + (string_table[string_table_index + 2] or 0)) % 16777216

            local chain_index
            local cur_chain
            local hash_chain = hash_tables[hash]
            local chain_old_size
            if not hash_chain then
                chain_old_size = 0
                hash_chain = {}
                hash_tables[hash] = hash_chain
                if dict_hash_tables then
                    cur_chain = dict_hash_tables[hash]
                    chain_index = cur_chain and #cur_chain or 0
                else
                    chain_index = 0
                end
            else
                chain_old_size = #hash_chain
                cur_chain = hash_chain
                chain_index = chain_old_size
            end

            if index <= block_end then hash_chain[chain_old_size + 1] = index end

            if (chain_index > 0 and index + 2 <= block_end and
                (not config_use_lazy or prev_len < config_max_lazy_match)) then

                local depth =
                    (config_use_lazy and prev_len >= config_good_prev_length) and
                    config_good_hash_chain or config_max_hash_chain

                local max_len_minus_one = block_end - index
                max_len_minus_one = (max_len_minus_one >= 257) and 257 or
                    max_len_minus_one
                max_len_minus_one = max_len_minus_one + string_table_index
                local string_table_index_plus_three = string_table_index + 3

                while chain_index >= 1 and depth > 0 do
                    local prev = cur_chain[chain_index]

                    if index - prev > 32768 then break end
                    if prev < index then
                        local sj = string_table_index_plus_three

                        if prev >= -257 then
                            local pj = prev - offset_minus_three
                            while (sj <= max_len_minus_one and string_table[pj] ==
                                string_table[sj]) do
                                sj = sj + 1
                                pj = pj + 1
                            end
                        else
                            local pj = dict_string_len_plus3 + prev
                            while (sj <= max_len_minus_one and dict_string_table[pj] ==
                                string_table[sj]) do
                                sj = sj + 1
                                pj = pj + 1
                            end
                        end
                        local j = sj - string_table_index
                        if j > cur_len then
                            cur_len = j
                            cur_dist = index - prev
                        end
                        if cur_len >= config_nice_length then break end
                    end

                    chain_index = chain_index - 1
                    depth = depth - 1
                    if chain_index == 0 and prev > 0 and dict_hash_tables then
                        cur_chain = dict_hash_tables[hash]
                        chain_index = cur_chain and #cur_chain or 0
                    end
                end
            end

            if not config_use_lazy then prev_len, prev_dist = cur_len, cur_dist end
            if ((not config_use_lazy or match_available) and
                (prev_len > 3 or (prev_len == 3 and prev_dist < 4096)) and cur_len <=
                prev_len) then
                local code = _length_to_deflate_code[prev_len]
                local length_extra_bits_bitlen = _length_to_deflate_extra_bitlen[prev_len]
                local dist_code, dist_extra_bits_bitlen, dist_extra_bits
                if prev_dist <= 256 then -- have cached code for small distance.
                    dist_code = _dist256_to_deflate_code[prev_dist]
                    dist_extra_bits = _dist256_to_deflate_extra_bits[prev_dist]
                    dist_extra_bits_bitlen = _dist256_to_deflate_extra_bitlen[prev_dist]
                else
                    dist_code = 16
                    dist_extra_bits_bitlen = 7
                    local a = 384
                    local b = 512

                    while true do
                        if prev_dist <= a then
                            dist_extra_bits = (prev_dist - (b / 2) - 1) % (b / 4)
                            break
                        elseif prev_dist <= b then
                            dist_extra_bits = (prev_dist - (b / 2) - 1) % (b / 4)
                            dist_code = dist_code + 1
                            break
                        else
                            dist_code = dist_code + 2
                            dist_extra_bits_bitlen = dist_extra_bits_bitlen + 1
                            a = a * 2
                            b = b * 2
                        end
                    end
                end
                lcode_tblsize = lcode_tblsize + 1
                lcodes[lcode_tblsize] = code
                lcodes_counts[code] = (lcodes_counts[code] or 0) + 1

                dcodes_tblsize = dcodes_tblsize + 1
                dcodes[dcodes_tblsize] = dist_code
                dcodes_counts[dist_code] = (dcodes_counts[dist_code] or 0) + 1

                if length_extra_bits_bitlen > 0 then
                    local lenExtraBits = _length_to_deflate_extra_bits[prev_len]
                    lextra_bits_tblsize = lextra_bits_tblsize + 1
                    lextra_bits[lextra_bits_tblsize] = lenExtraBits
                end
                if dist_extra_bits_bitlen > 0 then
                    dextra_bits_tblsize = dextra_bits_tblsize + 1
                    dextra_bits[dextra_bits_tblsize] = dist_extra_bits
                end

                for i = index + 1, index + prev_len - (config_use_lazy and 2 or 1) do
                    hash = (hash * 256 + (string_table[i - offset + 2] or 0)) % 16777216
                    if prev_len <= config_max_insert_length then
                        hash_chain = hash_tables[hash]
                        if not hash_chain then
                            hash_chain = {}
                            hash_tables[hash] = hash_chain
                        end
                        hash_chain[#hash_chain + 1] = i
                    end
                end
                index = index + prev_len - (config_use_lazy and 1 or 0)
                match_available = false
            elseif (not config_use_lazy) or match_available then
                local code = string_table[config_use_lazy and (string_table_index - 1) or
                    string_table_index]
                lcode_tblsize = lcode_tblsize + 1
                lcodes[lcode_tblsize] = code
                lcodes_counts[code] = (lcodes_counts[code] or 0) + 1
                index = index + 1
            else
                match_available = true
                index = index + 1
            end
        end

        -- Write "end of block" symbol
        lcode_tblsize = lcode_tblsize + 1
        lcodes[lcode_tblsize] = 256
        lcodes_counts[256] = (lcodes_counts[256] or 0) + 1

        return lcodes, lextra_bits, lcodes_counts, dcodes, dextra_bits, dcodes_counts
    end

    -- Get the header data of dynamic block.
    -- @param lcodes_count The count of each literal/LZ77_length codes.
    -- @param dcodes_count The count of each Lz77 distance codes.
    -- @return a lots of stuffs.
    -- @see RFC1951 Page 12
    local function GetBlockDynamicHuffmanHeader(lcodes_counts, dcodes_counts)
        local lcodes_huffman_bitlens, lcodes_huffman_codes, max_non_zero_bitlen_lcode =
            GetHuffmanBitlenAndCode(lcodes_counts, 15, 285)
        local dcodes_huffman_bitlens, dcodes_huffman_codes, max_non_zero_bitlen_dcode =
            GetHuffmanBitlenAndCode(dcodes_counts, 15, 29)

        local rle_deflate_codes, rle_extra_bits, rle_codes_counts =
            RunLengthEncodeHuffmanBitlen(lcodes_huffman_bitlens,
                max_non_zero_bitlen_lcode,
                dcodes_huffman_bitlens,
                max_non_zero_bitlen_dcode)

        local rle_codes_huffman_bitlens, rle_codes_huffman_codes =
            GetHuffmanBitlenAndCode(rle_codes_counts, 7, 18)

        local HCLEN = 0
        for i = 1, 19 do
            local symbol = _rle_codes_huffman_bitlen_order[i]
            local length = rle_codes_huffman_bitlens[symbol] or 0
            if length ~= 0 then HCLEN = i end
        end

        HCLEN = HCLEN - 4
        local HLIT = max_non_zero_bitlen_lcode + 1 - 257
        local HDIST = max_non_zero_bitlen_dcode + 1 - 1
        if HDIST < 0 then HDIST = 0 end

        return HLIT, HDIST, HCLEN, rle_codes_huffman_bitlens, rle_codes_huffman_codes,
        rle_deflate_codes, rle_extra_bits, lcodes_huffman_bitlens,
        lcodes_huffman_codes, dcodes_huffman_bitlens, dcodes_huffman_codes
    end

    -- Get the size of dynamic block without writing any bits into the writer.
    -- @param ... Read the source code of GetBlockDynamicHuffmanHeader()
    -- @return the bit length of the dynamic block
    local function GetDynamicHuffmanBlockSize(lcodes, dcodes, HCLEN,
        rle_codes_huffman_bitlens,
        rle_deflate_codes,
        lcodes_huffman_bitlens,
        dcodes_huffman_bitlens)

        local block_bitlen = 17 -- 1+2+5+5+4
        block_bitlen = block_bitlen + (HCLEN + 4) * 3

        for i = 1, #rle_deflate_codes do
            local code = rle_deflate_codes[i]
            block_bitlen = block_bitlen + rle_codes_huffman_bitlens[code]
            if code >= 16 then
                block_bitlen = block_bitlen +
                    ((code == 16) and 2 or (code == 17 and 3 or 7))
            end
        end

        local length_code_count = 0
        for i = 1, #lcodes do
            local code = lcodes[i]
            local huffman_bitlen = lcodes_huffman_bitlens[code]
            block_bitlen = block_bitlen + huffman_bitlen
            if code > 256 then -- Length code
                length_code_count = length_code_count + 1
                if code > 264 and code < 285 then -- Length code with extra bits
                    local extra_bits_bitlen = _literal_deflate_code_to_extra_bitlen[code -
                        256]
                    block_bitlen = block_bitlen + extra_bits_bitlen
                end
                local dist_code = dcodes[length_code_count]
                local dist_huffman_bitlen = dcodes_huffman_bitlens[dist_code]
                block_bitlen = block_bitlen + dist_huffman_bitlen

                if dist_code > 3 then -- dist code with extra bits
                    local dist_extra_bits_bitlen = (dist_code - dist_code % 2) / 2 - 1
                    block_bitlen = block_bitlen + dist_extra_bits_bitlen
                end
            end
        end
        return block_bitlen
    end

    -- Write dynamic block.
    -- @param ... Read the source code of GetBlockDynamicHuffmanHeader()
    local function CompressDynamicHuffmanBlock(WriteBits, is_last_block, lcodes,
        lextra_bits, dcodes, dextra_bits,
        HLIT, HDIST, HCLEN,
        rle_codes_huffman_bitlens,
        rle_codes_huffman_codes,
        rle_deflate_codes, rle_extra_bits,
        lcodes_huffman_bitlens,
        lcodes_huffman_codes,
        dcodes_huffman_bitlens,
        dcodes_huffman_codes)

        WriteBits(is_last_block and 1 or 0, 1) -- Last block identifier
        WriteBits(2, 2) -- Dynamic Huffman block identifier

        WriteBits(HLIT, 5)
        WriteBits(HDIST, 5)
        WriteBits(HCLEN, 4)

        for i = 1, HCLEN + 4 do
            local symbol = _rle_codes_huffman_bitlen_order[i]
            local length = rle_codes_huffman_bitlens[symbol] or 0
            WriteBits(length, 3)
        end

        local rleExtraBitsIndex = 1
        for i = 1, #rle_deflate_codes do
            local code = rle_deflate_codes[i]
            WriteBits(rle_codes_huffman_codes[code], rle_codes_huffman_bitlens[code])
            if code >= 16 then
                local extraBits = rle_extra_bits[rleExtraBitsIndex]
                WriteBits(extraBits, (code == 16) and 2 or (code == 17 and 3 or 7))
                rleExtraBitsIndex = rleExtraBitsIndex + 1
            end
        end

        local length_code_count = 0
        local length_code_with_extra_count = 0
        local dist_code_with_extra_count = 0

        for i = 1, #lcodes do
            local deflate_codee = lcodes[i]
            local huffman_code = lcodes_huffman_codes[deflate_codee]
            local huffman_bitlen = lcodes_huffman_bitlens[deflate_codee]
            WriteBits(huffman_code, huffman_bitlen)
            if deflate_codee > 256 then -- Length code
                length_code_count = length_code_count + 1
                if deflate_codee > 264 and deflate_codee < 285 then
                    -- Length code with extra bits
                    length_code_with_extra_count = length_code_with_extra_count + 1
                    local extra_bits = lextra_bits[length_code_with_extra_count]
                    local extra_bits_bitlen =
                        _literal_deflate_code_to_extra_bitlen[deflate_codee - 256]
                    WriteBits(extra_bits, extra_bits_bitlen)
                end
                -- Write distance code
                local dist_deflate_code = dcodes[length_code_count]
                local dist_huffman_code = dcodes_huffman_codes[dist_deflate_code]
                local dist_huffman_bitlen = dcodes_huffman_bitlens[dist_deflate_code]
                WriteBits(dist_huffman_code, dist_huffman_bitlen)

                if dist_deflate_code > 3 then -- dist code with extra bits
                    dist_code_with_extra_count = dist_code_with_extra_count + 1
                    local dist_extra_bits = dextra_bits[dist_code_with_extra_count]
                    local dist_extra_bits_bitlen = (dist_deflate_code - dist_deflate_code %
                        2) / 2 - 1
                    WriteBits(dist_extra_bits, dist_extra_bits_bitlen)
                end
            end
        end
    end

    -- Get the size of fixed block without writing any bits into the writer.
    -- @param lcodes literal/LZ77_length deflate codes
    -- @param decodes LZ77 distance deflate codes
    -- @return the bit length of the fixed block
    local function GetFixedHuffmanBlockSize(lcodes, dcodes)
        local block_bitlen = 3
        local length_code_count = 0
        for i = 1, #lcodes do
            local code = lcodes[i]
            local huffman_bitlen = _fix_block_literal_huffman_bitlen[code]
            block_bitlen = block_bitlen + huffman_bitlen
            if code > 256 then -- Length code
                length_code_count = length_code_count + 1
                if code > 264 and code < 285 then -- Length code with extra bits
                    local extra_bits_bitlen = _literal_deflate_code_to_extra_bitlen[code -
                        256]
                    block_bitlen = block_bitlen + extra_bits_bitlen
                end
                local dist_code = dcodes[length_code_count]
                block_bitlen = block_bitlen + 5

                if dist_code > 3 then -- dist code with extra bits
                    local dist_extra_bits_bitlen = (dist_code - dist_code % 2) / 2 - 1
                    block_bitlen = block_bitlen + dist_extra_bits_bitlen
                end
            end
        end
        return block_bitlen
    end

    -- Write fixed block.
    -- @param lcodes literal/LZ77_length deflate codes
    -- @param decodes LZ77 distance deflate codes
    local function CompressFixedHuffmanBlock(WriteBits, is_last_block, lcodes,
        lextra_bits, dcodes, dextra_bits)
        WriteBits(is_last_block and 1 or 0, 1) -- Last block identifier
        WriteBits(1, 2) -- Fixed Huffman block identifier
        local length_code_count = 0
        local length_code_with_extra_count = 0
        local dist_code_with_extra_count = 0
        for i = 1, #lcodes do
            local deflate_code = lcodes[i]
            local huffman_code = _fix_block_literal_huffman_code[deflate_code]
            local huffman_bitlen = _fix_block_literal_huffman_bitlen[deflate_code]
            WriteBits(huffman_code, huffman_bitlen)
            if deflate_code > 256 then -- Length code
                length_code_count = length_code_count + 1
                if deflate_code > 264 and deflate_code < 285 then
                    -- Length code with extra bits
                    length_code_with_extra_count = length_code_with_extra_count + 1
                    local extra_bits = lextra_bits[length_code_with_extra_count]
                    local extra_bits_bitlen =
                        _literal_deflate_code_to_extra_bitlen[deflate_code - 256]
                    WriteBits(extra_bits, extra_bits_bitlen)
                end
                -- Write distance code
                local dist_code = dcodes[length_code_count]
                local dist_huffman_code = _fix_block_dist_huffman_code[dist_code]
                WriteBits(dist_huffman_code, 5)

                if dist_code > 3 then -- dist code with extra bits
                    dist_code_with_extra_count = dist_code_with_extra_count + 1
                    local dist_extra_bits = dextra_bits[dist_code_with_extra_count]
                    local dist_extra_bits_bitlen = (dist_code - dist_code % 2) / 2 - 1
                    WriteBits(dist_extra_bits, dist_extra_bits_bitlen)
                end
            end
        end
    end

    -- Get the size of store block without writing any bits into the writer.
    -- @param block_start The start index of the origin input string
    -- @param block_end The end index of the origin input string
    -- @param Total bit lens had been written into the compressed result before,
    -- because store block needs to shift to byte boundary.
    -- @return the bit length of the fixed block
    local function GetStoreBlockSize(block_start, block_end, total_bitlen)
        assert(block_end - block_start + 1 <= 65535)
        local block_bitlen = 3
        total_bitlen = total_bitlen + 3
        local padding_bitlen = (8 - total_bitlen % 8) % 8
        block_bitlen = block_bitlen + padding_bitlen
        block_bitlen = block_bitlen + 32
        block_bitlen = block_bitlen + (block_end - block_start + 1) * 8
        return block_bitlen
    end

    -- Write the store block.
    -- @param ... lots of stuffs
    -- @return nil
    local function CompressStoreBlock(WriteBits, WriteString, is_last_block, str,
        block_start, block_end, total_bitlen)
        assert(block_end - block_start + 1 <= 65535)
        WriteBits(is_last_block and 1 or 0, 1) -- Last block identifer.
        WriteBits(0, 2) -- Store block identifier.
        total_bitlen = total_bitlen + 3
        local padding_bitlen = (8 - total_bitlen % 8) % 8
        if padding_bitlen > 0 then
            WriteBits(_pow2[padding_bitlen] - 1, padding_bitlen)
        end
        local size = block_end - block_start + 1
        WriteBits(size, 16)

        -- Write size's one's complement
        local comp = (255 - size % 256) + (255 - (size - size % 256) / 256) * 256
        WriteBits(comp, 16)

        WriteString(str:sub(block_start, block_end))
    end

    -- Do the deflate
    -- Currently using a simple way to determine the block size
    -- (This is why the compression ratio is little bit worse than zlib when
    -- the input size is very large
    -- The first block is 64KB, the following block is 32KB.
    -- After each block, there is a memory cleanup operation.
    -- This is not a fast operation, but it is needed to save memory usage, so
    -- the memory usage does not grow unboundly. If the data size is less than
    -- 64KB, then memory cleanup won't happen.
    -- This function determines whether to use store/fixed/dynamic blocks by
    -- calculating the block size of each block type and chooses the smallest one.
    local function Deflate(configs, WriteBits, WriteString, FlushWriter, str,
        dictionary)
        local string_table = {}
        local hash_tables = {}
        local is_last_block = nil
        local block_start
        local block_end
        local bitlen_written
        local total_bitlen = FlushWriter(_FLUSH_MODE_NO_FLUSH)
        local strlen = #str
        local offset

        local level
        local strategy
        if configs then
            if configs.level then level = configs.level end
            if configs.strategy then strategy = configs.strategy end
        end

        if not level then
            if strlen < 2048 then
                level = 7
            elseif strlen > 65536 then
                level = 3
            else
                level = 5
            end
        end

        while not is_last_block do
            if not block_start then
                block_start = 1
                block_end = 64 * 1024 - 1
                offset = 0
            else
                block_start = block_end + 1
                block_end = block_end + 32 * 1024
                offset = block_start - 32 * 1024 - 1
            end

            if block_end >= strlen then
                block_end = strlen
                is_last_block = true
            else
                is_last_block = false
            end

            local lcodes, lextra_bits, lcodes_counts, dcodes, dextra_bits, dcodes_counts

            local HLIT, HDIST, HCLEN, rle_codes_huffman_bitlens,
            rle_codes_huffman_codes, rle_deflate_codes, rle_extra_bits,
            lcodes_huffman_bitlens, lcodes_huffman_codes, dcodes_huffman_bitlens,
            dcodes_huffman_codes

            local dynamic_block_bitlen
            local fixed_block_bitlen
            local store_block_bitlen

            if level ~= 0 then

                -- GetBlockLZ77 needs block_start to block_end+3 to be loaded.
                LoadStringToTable(str, string_table, block_start, block_end + 3, offset)
                if block_start == 1 and dictionary then
                    local dict_string_table = dictionary.string_table
                    local dict_strlen = dictionary.strlen
                    for i = 0, (-dict_strlen + 1) < -257 and -257 or (-dict_strlen + 1), -1 do
                        string_table[i] = dict_string_table[dict_strlen + i]
                    end
                end

                if strategy == "huffman_only" then
                    lcodes = {}
                    LoadStringToTable(str, lcodes, block_start, block_end, block_start - 1)
                    lextra_bits = {}
                    lcodes_counts = {}
                    lcodes[block_end - block_start + 2] = 256 -- end of block
                    for i = 1, block_end - block_start + 2 do
                        local code = lcodes[i]
                        lcodes_counts[code] = (lcodes_counts[code] or 0) + 1
                    end
                    dcodes = {}
                    dextra_bits = {}
                    dcodes_counts = {}
                else
                    lcodes, lextra_bits, lcodes_counts, dcodes, dextra_bits, dcodes_counts =
                        GetBlockLZ77Result(level, string_table, hash_tables, block_start,
                            block_end, offset, dictionary)
                end

                -- LuaFormatter off
                HLIT, HDIST, HCLEN, rle_codes_huffman_bitlens, rle_codes_huffman_codes, rle_deflate_codes,
                rle_extra_bits, lcodes_huffman_bitlens, lcodes_huffman_codes, dcodes_huffman_bitlens, dcodes_huffman_codes =
                    -- LuaFormatter on
                    GetBlockDynamicHuffmanHeader(lcodes_counts, dcodes_counts)
                dynamic_block_bitlen = GetDynamicHuffmanBlockSize(lcodes, dcodes, HCLEN,
                    rle_codes_huffman_bitlens,
                    rle_deflate_codes,
                    lcodes_huffman_bitlens,
                    dcodes_huffman_bitlens)
                fixed_block_bitlen = GetFixedHuffmanBlockSize(lcodes, dcodes)
            end

            store_block_bitlen = GetStoreBlockSize(block_start, block_end, total_bitlen)

            local min_bitlen = store_block_bitlen
            min_bitlen = (fixed_block_bitlen and fixed_block_bitlen < min_bitlen) and
                fixed_block_bitlen or min_bitlen
            min_bitlen =
                (dynamic_block_bitlen and dynamic_block_bitlen < min_bitlen) and
                dynamic_block_bitlen or min_bitlen

            if level == 0 or
                (strategy ~= "fixed" and strategy ~= "dynamic" and store_block_bitlen ==
                    min_bitlen) then
                CompressStoreBlock(WriteBits, WriteString, is_last_block, str,
                    block_start, block_end, total_bitlen)
                total_bitlen = total_bitlen + store_block_bitlen
            elseif strategy ~= "dynamic" and
                (strategy == "fixed" or fixed_block_bitlen == min_bitlen) then
                CompressFixedHuffmanBlock(WriteBits, is_last_block, lcodes, lextra_bits,
                    dcodes, dextra_bits)
                total_bitlen = total_bitlen + fixed_block_bitlen
            elseif strategy == "dynamic" or dynamic_block_bitlen == min_bitlen then
                CompressDynamicHuffmanBlock(WriteBits, is_last_block, lcodes, lextra_bits,
                    dcodes, dextra_bits, HLIT, HDIST, HCLEN,
                    rle_codes_huffman_bitlens,
                    rle_codes_huffman_codes, rle_deflate_codes,
                    rle_extra_bits, lcodes_huffman_bitlens,
                    lcodes_huffman_codes, dcodes_huffman_bitlens,
                    dcodes_huffman_codes)
                total_bitlen = total_bitlen + dynamic_block_bitlen
            end

            if is_last_block then
                bitlen_written = FlushWriter(_FLUSH_MODE_NO_FLUSH)
            else
                bitlen_written = FlushWriter(_FLUSH_MODE_MEMORY_CLEANUP)
            end

            assert(bitlen_written == total_bitlen)

            -- Memory clean up, so memory consumption does not always grow linearly
            -- , even if input string is > 64K.
            -- Not a very efficient operation, but this operation won't happen
            -- when the input data size is less than 64K.
            if not is_last_block then
                local j
                if dictionary and block_start == 1 then
                    j = 0
                    while (string_table[j]) do
                        string_table[j] = nil
                        j = j - 1
                    end
                end
                dictionary = nil
                j = 1
                for i = block_end - 32767, block_end do
                    string_table[j] = string_table[i - offset]
                    j = j + 1
                end

                for k, t in pairs(hash_tables) do
                    local tSize = #t
                    if tSize > 0 and block_end + 1 - t[1] > 32768 then
                        if tSize == 1 then
                            hash_tables[k] = nil
                        else
                            local new = {}
                            local newSize = 0
                            for i = 2, tSize do
                                j = t[i]
                                if block_end + 1 - j <= 32768 then
                                    newSize = newSize + 1
                                    new[newSize] = j
                                end
                            end
                            hash_tables[k] = new
                        end
                    end
                end
            end
        end
    end

    --- The description to compression configuration table. <br>
    -- Any field can be nil to use its default. <br>
    -- Table with keys other than those below is an invalid table.
    -- @class table
    -- @name compression_configs
    -- @field level The compression level ranged from 0 to 9. 0 is no compression.
    -- 9 is the slowest but best compression. Use nil for default level.
    -- @field strategy The compression strategy. "fixed" to only use fixed deflate
    -- compression block. "dynamic" to only use dynamic block. "huffman_only" to
    -- do no LZ77 compression. Only do huffman compression.

    -- @see LibDeflate:CompressDeflate(str, configs)
    -- @see LibDeflate:CompressDeflateWithDict(str, dictionary, configs)
    local function CompressDeflateInternal(str, dictionary, configs)
        local WriteBits, WriteString, FlushWriter = CreateWriter()
        Deflate(configs, WriteBits, WriteString, FlushWriter, str, dictionary)
        local total_bitlen, result = FlushWriter(_FLUSH_MODE_OUTPUT)
        local padding_bitlen = (8 - total_bitlen % 8) % 8
        return result, padding_bitlen
    end

    -- @see LibDeflate:CompressZlib
    -- @see LibDeflate:CompressZlibWithDict
    local function CompressZlibInternal(str, dictionary, configs)
        local WriteBits, WriteString, FlushWriter = CreateWriter()

        local CM = 8 -- Compression method
        local CINFO = 7 -- Window Size = 32K
        local CMF = CINFO * 16 + CM
        WriteBits(CMF, 8)

        local FDIST = dictionary and 1 or 0
        local FLEVEL = 2 -- Default compression
        local FLG = FLEVEL * 64 + FDIST * 32
        local FCHECK = (31 - (CMF * 256 + FLG) % 31)
        -- The FCHECK value must be such that CMF and FLG,
        -- when viewed as a 16-bit unsigned integer stored
        -- in MSB order (CMF*256 + FLG), is a multiple of 31.
        FLG = FLG + FCHECK
        WriteBits(FLG, 8)

        if FDIST == 1 then
            local adler32 = dictionary.adler32
            local byte0 = adler32 % 256
            adler32 = (adler32 - byte0) / 256
            local byte1 = adler32 % 256
            adler32 = (adler32 - byte1) / 256
            local byte2 = adler32 % 256
            adler32 = (adler32 - byte2) / 256
            local byte3 = adler32 % 256
            WriteBits(byte3, 8)
            WriteBits(byte2, 8)
            WriteBits(byte1, 8)
            WriteBits(byte0, 8)
        end

        Deflate(configs, WriteBits, WriteString, FlushWriter, str, dictionary)
        FlushWriter(_FLUSH_MODE_BYTE_BOUNDARY)

        local adler32 = LibDeflate:Adler32(str)

        -- Most significant byte first
        local byte3 = adler32 % 256
        adler32 = (adler32 - byte3) / 256
        local byte2 = adler32 % 256
        adler32 = (adler32 - byte2) / 256
        local byte1 = adler32 % 256
        adler32 = (adler32 - byte1) / 256
        local byte0 = adler32 % 256

        WriteBits(byte0, 8)
        WriteBits(byte1, 8)
        WriteBits(byte2, 8)
        WriteBits(byte3, 8)
        local total_bitlen, result = FlushWriter(_FLUSH_MODE_OUTPUT)
        local padding_bitlen = (8 - total_bitlen % 8) % 8
        return result, padding_bitlen
    end

    --- Compress using the raw deflate format.
    -- @param str [string] The data to be compressed.
    -- @param configs [table/nil] The configuration table to control the compression
    -- . If nil, use the default configuration.
    -- @return [string] The compressed data.
    -- @return [integer] The number of bits padded at the end of output.
    -- 0 <= bits < 8  <br>
    -- This means the most significant "bits" of the last byte of the returned
    -- compressed data are padding bits and they don't affect decompression.
    -- You don't need to use this value unless you want to do some postprocessing
    -- to the compressed data.
    -- @see compression_configs
    -- @see LibDeflate:DecompressDeflate
    function deflate_compress(str, configs)
        local arg_valid, arg_err = IsValidArguments(str, false, nil, true, configs)
        if not arg_valid then
            error(("Usage: LibDeflate:CompressDeflate(str, configs): " .. arg_err), 2)
        end
        return CompressDeflateInternal(str, nil, configs)
    end

    --- Compress using the raw deflate format with a preset dictionary.
    -- @param str [string] The data to be compressed.
    -- @param dictionary [table] The preset dictionary produced by
    -- LibDeflate:CreateDictionary
    -- @param configs [table/nil] The configuration table to control the compression
    -- . If nil, use the default configuration.
    -- @return [string] The compressed data.
    -- @return [integer] The number of bits padded at the end of output.
    -- 0 <= bits < 8  <br>
    -- This means the most significant "bits" of the last byte of the returned
    -- compressed data are padding bits and they don't affect decompression.
    -- You don't need to use this value unless you want to do some postprocessing
    -- to the compressed data.
    -- @see compression_configs
    -- @see LibDeflate:CreateDictionary
    -- @see LibDeflate:DecompressDeflateWithDict


    --- Compress using the zlib format.
    -- @param str [string] the data to be compressed.
    -- @param configs [table/nil] The configuration table to control the compression
    -- . If nil, use the default configuration.
    -- @return [string] The compressed data.
    -- @return [integer] The number of bits padded at the end of output.
    -- Should always be 0.
    -- Zlib formatted compressed data never has padding bits at the end.
    -- @see compression_configs
    -- @see LibDeflate:DecompressZlib
    function zlib_compress(str, configs)
        local arg_valid, arg_err = IsValidArguments(str, false, nil, true, configs)
        if not arg_valid then
            error(("Usage: LibDeflate:CompressZlib(str, configs): " .. arg_err), 2)
        end
        return CompressZlibInternal(str, nil, configs)
    end

--[[ --------------------------------------------------------------------------
	Decompress code
--]] --------------------------------------------------------------------------

--[[
	Create a reader to easily reader stuffs as the unit of bits.
	Return values:
	1. ReadBits(bitlen)
	2. ReadBytes(bytelen, buffer, buffer_size)
	3. Decode(huffman_bitlen_count, huffman_symbol, min_bitlen)
	4. ReaderBitlenLeft()
	5. SkipToByteBoundary()
--]]
    local function CreateReader(input_string)
        local input = input_string
        local input_strlen = #input_string
        local input_next_byte_pos = 1
        local cache_bitlen = 0
        local cache = 0

        -- Read some bits.
        -- To improve speed, this function does not
        -- check if the input has been exhausted.
        -- Use ReaderBitlenLeft() < 0 to check it.
        -- @param bitlen the number of bits to read
        -- @return the data is read.
        local function ReadBits(bitlen)
            local rshift_mask = _pow2[bitlen]
            local code
            if bitlen <= cache_bitlen then
                code = cache % rshift_mask
                cache = (cache - code) / rshift_mask
                cache_bitlen = cache_bitlen - bitlen
            else -- Whether input has been exhausted is not checked.
                local lshift_mask = _pow2[cache_bitlen]
                local byte1, byte2, byte3, byte4 =
                    string.byte(input, input_next_byte_pos, input_next_byte_pos + 3)
                -- This requires lua number to be at least double ()
                cache = cache +
                    ((byte1 or 0) + (byte2 or 0) * 256 + (byte3 or 0) * 65536 +
                        (byte4 or 0) * 16777216) * lshift_mask
                input_next_byte_pos = input_next_byte_pos + 4
                cache_bitlen = cache_bitlen + 32 - bitlen
                code = cache % rshift_mask
                cache = (cache - code) / rshift_mask
            end
            return code
        end

        -- Read some bytes from the reader.
        -- Assume reader is on the byte boundary.
        -- @param bytelen The number of bytes to be read.
        -- @param buffer The byte read will be stored into this buffer.
        -- @param buffer_size The buffer will be modified starting from
        --	buffer[buffer_size+1], ending at buffer[buffer_size+bytelen-1]
        -- @return the new buffer_size
        local function ReadBytes(bytelen, buffer, buffer_size)
            assert(cache_bitlen % 8 == 0)

            local byte_from_cache =
                (cache_bitlen / 8 < bytelen) and (cache_bitlen / 8) or bytelen
            for _ = 1, byte_from_cache do
                local byte = cache % 256
                buffer_size = buffer_size + 1
                buffer[buffer_size] = string.char(byte)
                cache = (cache - byte) / 256
            end
            cache_bitlen = cache_bitlen - byte_from_cache * 8
            bytelen = bytelen - byte_from_cache
            if (input_strlen - input_next_byte_pos - bytelen + 1) * 8 + cache_bitlen < 0 then
                return -1 -- out of input
            end
            for i = input_next_byte_pos, input_next_byte_pos + bytelen - 1 do
                buffer_size = buffer_size + 1
                buffer[buffer_size] = string.sub(input, i, i)
            end

            input_next_byte_pos = input_next_byte_pos + bytelen
            return buffer_size
        end

        -- Decode huffman code
        -- To improve speed, this function does not check
        -- if the input has been exhausted.
        -- Use ReaderBitlenLeft() < 0 to check it.
        -- Credits for Mark Adler. This code is from puff:Decode()
        -- @see puff:Decode(...)
        -- @param huffman_bitlen_count
        -- @param huffman_symbol
        -- @param min_bitlen The minimum huffman bit length of all symbols
        -- @return The decoded deflate code.
        --	Negative value is returned if decoding fails.
        local function Decode(huffman_bitlen_counts, huffman_symbols, min_bitlen)
            local code = 0
            local first = 0
            local index = 0
            local count
            if min_bitlen > 0 then
                if cache_bitlen < 15 and input then
                    local lshift_mask = _pow2[cache_bitlen]
                    local byte1, byte2, byte3, byte4 =
                        string.byte(input, input_next_byte_pos, input_next_byte_pos + 3)
                    -- This requires lua number to be at least double ()
                    cache = cache +
                        ((byte1 or 0) + (byte2 or 0) * 256 + (byte3 or 0) * 65536 +
                            (byte4 or 0) * 16777216) * lshift_mask
                    input_next_byte_pos = input_next_byte_pos + 4
                    cache_bitlen = cache_bitlen + 32
                end

                local rshift_mask = _pow2[min_bitlen]
                cache_bitlen = cache_bitlen - min_bitlen
                code = cache % rshift_mask
                cache = (cache - code) / rshift_mask
                -- Reverse the bits
                code = _reverse_bits_tbl[min_bitlen][code]

                count = huffman_bitlen_counts[min_bitlen]
                if code < count then return huffman_symbols[code] end
                index = count
                first = count * 2
                code = code * 2
            end

            for bitlen = min_bitlen + 1, 15 do
                local bit
                bit = cache % 2
                cache = (cache - bit) / 2
                cache_bitlen = cache_bitlen - 1

                code = (bit == 1) and (code + 1 - code % 2) or code
                count = huffman_bitlen_counts[bitlen] or 0
                local diff = code - first
                if diff < count then return huffman_symbols[index + diff] end
                index = index + count
                first = first + count
                first = first * 2
                code = code * 2
            end
            -- invalid literal/length or distance code
            -- in fixed or dynamic block (run out of code)
            return -10
        end

        local function ReaderBitlenLeft()
            return (input_strlen - input_next_byte_pos + 1) * 8 + cache_bitlen
        end

        local function SkipToByteBoundary()
            local skipped_bitlen = cache_bitlen % 8
            local rshift_mask = _pow2[skipped_bitlen]
            cache_bitlen = cache_bitlen - skipped_bitlen
            cache = (cache - cache % rshift_mask) / rshift_mask
        end

        return ReadBits, ReadBytes, Decode, ReaderBitlenLeft, SkipToByteBoundary
    end

    -- Create a deflate state, so I can pass in less arguments to functions.
    -- @param str the whole string to be decompressed.
    -- @param dictionary The preset dictionary. nil if not provided.
    --		This dictionary should be produced by LibDeflate:CreateDictionary(str)
    -- @return The decomrpess state.
    local function CreateDecompressState(str, dictionary)
        local ReadBits, ReadBytes, Decode, ReaderBitlenLeft, SkipToByteBoundary =
            CreateReader(str)
        local state = {
            ReadBits = ReadBits,
            ReadBytes = ReadBytes,
            Decode = Decode,
            ReaderBitlenLeft = ReaderBitlenLeft,
            SkipToByteBoundary = SkipToByteBoundary,
            buffer_size = 0,
            buffer = {},
            result_buffer = {},
            dictionary = dictionary
        }
        return state
    end

    -- Get the stuffs needed to decode huffman codes
    -- @see puff.c:construct(...)
    -- @param huffman_bitlen The huffman bit length of the huffman codes.
    -- @param max_symbol The maximum symbol
    -- @param max_bitlen The min huffman bit length of all codes
    -- @return zero or positive for success, negative for failure.
    -- @return The count of each huffman bit length.
    -- @return A table to convert huffman codes to deflate codes.
    -- @return The minimum huffman bit length.
    local function GetHuffmanForDecode(huffman_bitlens, max_symbol, max_bitlen)
        local huffman_bitlen_counts = {}
        local min_bitlen = max_bitlen
        for symbol = 0, max_symbol do
            local bitlen = huffman_bitlens[symbol] or 0
            min_bitlen = (bitlen > 0 and bitlen < min_bitlen) and bitlen or min_bitlen
            huffman_bitlen_counts[bitlen] = (huffman_bitlen_counts[bitlen] or 0) + 1
        end

        if huffman_bitlen_counts[0] == max_symbol + 1 then -- No Codes
            return 0, huffman_bitlen_counts, {}, 0 -- Complete, but decode will fail
        end

        local left = 1
        for len = 1, max_bitlen do
            left = left * 2
            left = left - (huffman_bitlen_counts[len] or 0)
            if left < 0 then
                return left -- Over-subscribed, return negative
            end
        end

        -- Generate offsets info symbol table for each length for sorting
        local offsets = {}
        offsets[1] = 0
        for len = 1, max_bitlen - 1 do
            offsets[len + 1] = offsets[len] + (huffman_bitlen_counts[len] or 0)
        end

        local huffman_symbols = {}
        for symbol = 0, max_symbol do
            local bitlen = huffman_bitlens[symbol] or 0
            if bitlen ~= 0 then
                local offset = offsets[bitlen]
                huffman_symbols[offset] = symbol
                offsets[bitlen] = offsets[bitlen] + 1
            end
        end

        -- Return zero for complete set, positive for incomplete set.
        return left, huffman_bitlen_counts, huffman_symbols, min_bitlen
    end

    -- Decode a fixed or dynamic huffman blocks, excluding last block identifier
    -- and block type identifer.
    -- @see puff.c:codes()
    -- @param state decompression state that will be modified by this function.
    --	@see CreateDecompressState
    -- @param ... Read the source code
    -- @return 0 on success, other value on failure.
    local function DecodeUntilEndOfBlock(state, lcodes_huffman_bitlens,
        lcodes_huffman_symbols,
        lcodes_huffman_min_bitlen,
        dcodes_huffman_bitlens,
        dcodes_huffman_symbols,
        dcodes_huffman_min_bitlen)
        local buffer, buffer_size, ReadBits, Decode, ReaderBitlenLeft, result_buffer =
            state.buffer, state.buffer_size, state.ReadBits, state.Decode,
        state.ReaderBitlenLeft, state.result_buffer
        local dictionary = state.dictionary
        local dict_string_table
        local dict_strlen

        local buffer_end = 1
        if dictionary and not buffer[0] then
            -- If there is a dictionary, copy the last 258 bytes into
            -- the string_table to make the copy in the main loop quicker.
            -- This is done only once per decompression.
            dict_string_table = dictionary.string_table
            dict_strlen = dictionary.strlen
            buffer_end = -dict_strlen + 1
            for i = 0, (-dict_strlen + 1) < -257 and -257 or (-dict_strlen + 1), -1 do
                buffer[i] = _byte_to_char[dict_string_table[dict_strlen + i]]
            end
        end

        repeat
            local symbol = Decode(lcodes_huffman_bitlens, lcodes_huffman_symbols,
                lcodes_huffman_min_bitlen)
            if symbol < 0 or symbol > 285 then
                -- invalid literal/length or distance code in fixed or dynamic block
                return -10
            elseif symbol < 256 then -- Literal
                buffer_size = buffer_size + 1
                buffer[buffer_size] = _byte_to_char[symbol]
            elseif symbol > 256 then -- Length code
                symbol = symbol - 256
                local bitlen = _literal_deflate_code_to_base_len[symbol]
                bitlen = (symbol >= 8) and
                    (bitlen +
                        ReadBits(_literal_deflate_code_to_extra_bitlen[symbol])) or
                    bitlen
                symbol = Decode(dcodes_huffman_bitlens, dcodes_huffman_symbols,
                    dcodes_huffman_min_bitlen)
                if symbol < 0 or symbol > 29 then
                    -- invalid literal/length or distance code in fixed or dynamic block
                    return -10
                end
                local dist = _dist_deflate_code_to_base_dist[symbol]
                dist = (dist > 4) and
                    (dist + ReadBits(_dist_deflate_code_to_extra_bitlen[symbol])) or
                    dist

                local char_buffer_index = buffer_size - dist + 1
                if char_buffer_index < buffer_end then
                    -- distance is too far back in fixed or dynamic block
                    return -11
                end
                if char_buffer_index >= -257 then
                    for _ = 1, bitlen do
                        buffer_size = buffer_size + 1
                        buffer[buffer_size] = buffer[char_buffer_index]
                        char_buffer_index = char_buffer_index + 1
                    end
                else
                    char_buffer_index = dict_strlen + char_buffer_index
                    for _ = 1, bitlen do
                        buffer_size = buffer_size + 1
                        buffer[buffer_size] =
                            _byte_to_char[dict_string_table[char_buffer_index]]
                        char_buffer_index = char_buffer_index + 1
                    end
                end
            end

            if ReaderBitlenLeft() < 0 then
                return 2 -- available inflate data did not terminate
            end

            if buffer_size >= 65536 then
                result_buffer[#result_buffer + 1] = table.concat(buffer, "", 1, 32768)
                for i = 32769, buffer_size do buffer[i - 32768] = buffer[i] end
                buffer_size = buffer_size - 32768
                buffer[buffer_size + 1] = nil
                -- NOTE: buffer[32769..end] and buffer[-257..0] are not cleared.
                -- This is why "buffer_size" variable is needed.
            end
        until symbol == 256

        state.buffer_size = buffer_size

        return 0
    end

    -- Decompress a store block
    -- @param state decompression state that will be modified by this function.
    -- @return 0 if succeeds, other value if fails.
    local function DecompressStoreBlock(state)
        local buffer, buffer_size, ReadBits, ReadBytes, ReaderBitlenLeft,
        SkipToByteBoundary, result_buffer = state.buffer, state.buffer_size,
        state.ReadBits, state.ReadBytes,
        state.ReaderBitlenLeft,
        state.SkipToByteBoundary,
        state.result_buffer

        SkipToByteBoundary()
        local bytelen = ReadBits(16)
        if ReaderBitlenLeft() < 0 then
            return 2 -- available inflate data did not terminate
        end
        local bytelenComp = ReadBits(16)
        if ReaderBitlenLeft() < 0 then
            return 2 -- available inflate data did not terminate
        end

        if bytelen % 256 + bytelenComp % 256 ~= 255 then
            return -2 -- Not one's complement
        end
        if (bytelen - bytelen % 256) / 256 + (bytelenComp - bytelenComp % 256) / 256 ~=
            255 then
            return -2 -- Not one's complement
        end

        -- Note that ReadBytes will skip to the next byte boundary first.
        buffer_size = ReadBytes(bytelen, buffer, buffer_size)
        if buffer_size < 0 then
            return 2 -- available inflate data did not terminate
        end

        -- memory clean up when there are enough bytes in the buffer.
        if buffer_size >= 65536 then
            result_buffer[#result_buffer + 1] = table.concat(buffer, "", 1, 32768)
            for i = 32769, buffer_size do buffer[i - 32768] = buffer[i] end
            buffer_size = buffer_size - 32768
            buffer[buffer_size + 1] = nil
        end
        state.buffer_size = buffer_size
        return 0
    end

    -- Decompress a fixed block
    -- @param state decompression state that will be modified by this function.
    -- @return 0 if succeeds other value if fails.
    local function DecompressFixBlock(state)
        return DecodeUntilEndOfBlock(state, _fix_block_literal_huffman_bitlen_count,
            _fix_block_literal_huffman_to_deflate_code, 7,
            _fix_block_dist_huffman_bitlen_count,
            _fix_block_dist_huffman_to_deflate_code, 5)
    end

    -- Decompress a dynamic block
    -- @param state decompression state that will be modified by this function.
    -- @return 0 if success, other value if fails.
    local function DecompressDynamicBlock(state)
        local ReadBits, Decode = state.ReadBits, state.Decode
        local nlen = ReadBits(5) + 257
        local ndist = ReadBits(5) + 1
        local ncode = ReadBits(4) + 4
        if nlen > 286 or ndist > 30 then
            -- dynamic block code description: too many length or distance codes
            return -3
        end

        local rle_codes_huffman_bitlens = {}

        for i = 1, ncode do
            rle_codes_huffman_bitlens[_rle_codes_huffman_bitlen_order[i]] = ReadBits(3)
        end

        local rle_codes_err, rle_codes_huffman_bitlen_counts,
        rle_codes_huffman_symbols, rle_codes_huffman_min_bitlen =
            GetHuffmanForDecode(rle_codes_huffman_bitlens, 18, 7)
        if rle_codes_err ~= 0 then -- Require complete code set here
            -- dynamic block code description: code lengths codes incomplete
            return -4
        end

        local lcodes_huffman_bitlens = {}
        local dcodes_huffman_bitlens = {}
        -- Read length/literal and distance code length tables
        local index = 0
        while index < nlen + ndist do
            local symbol -- Decoded value
            local bitlen -- Last length to repeat

            symbol = Decode(rle_codes_huffman_bitlen_counts, rle_codes_huffman_symbols,
                rle_codes_huffman_min_bitlen)

            if symbol < 0 then
                return symbol -- Invalid symbol
            elseif symbol < 16 then
                if index < nlen then
                    lcodes_huffman_bitlens[index] = symbol
                else
                    dcodes_huffman_bitlens[index - nlen] = symbol
                end
                index = index + 1
            else
                bitlen = 0
                if symbol == 16 then
                    if index == 0 then
                        -- dynamic block code description: repeat lengths
                        -- with no first length
                        return -5
                    end
                    if index - 1 < nlen then
                        bitlen = lcodes_huffman_bitlens[index - 1]
                    else
                        bitlen = dcodes_huffman_bitlens[index - nlen - 1]
                    end
                    symbol = 3 + ReadBits(2)
                elseif symbol == 17 then -- Repeat zero 3..10 times
                    symbol = 3 + ReadBits(3)
                else -- == 18, repeat zero 11.138 times
                    symbol = 11 + ReadBits(7)
                end
                if index + symbol > nlen + ndist then
                    -- dynamic block code description:
                    -- repeat more than specified lengths
                    return -6
                end
                while symbol > 0 do -- Repeat last or zero symbol times
                    symbol = symbol - 1
                    if index < nlen then
                        lcodes_huffman_bitlens[index] = bitlen
                    else
                        dcodes_huffman_bitlens[index - nlen] = bitlen
                    end
                    index = index + 1
                end
            end
        end

        if (lcodes_huffman_bitlens[256] or 0) == 0 then
            -- dynamic block code description: missing end-of-block code
            return -9
        end

        local lcodes_err, lcodes_huffman_bitlen_counts, lcodes_huffman_symbols,
        lcodes_huffman_min_bitlen = GetHuffmanForDecode(lcodes_huffman_bitlens,
            nlen - 1, 15)
        -- dynamic block code description: invalid literal/length code lengths,
        -- Incomplete code ok only for single length 1 code
        if (lcodes_err ~= 0 and
            (lcodes_err < 0 or nlen ~= (lcodes_huffman_bitlen_counts[0] or 0) +
                (lcodes_huffman_bitlen_counts[1] or 0))) then return -7 end

        local dcodes_err, dcodes_huffman_bitlen_counts, dcodes_huffman_symbols,
        dcodes_huffman_min_bitlen = GetHuffmanForDecode(dcodes_huffman_bitlens,
            ndist - 1, 15)
        -- dynamic block code description: invalid distance code lengths,
        -- Incomplete code ok only for single length 1 code
        if (dcodes_err ~= 0 and
            (dcodes_err < 0 or ndist ~= (dcodes_huffman_bitlen_counts[0] or 0) +
                (dcodes_huffman_bitlen_counts[1] or 0))) then return -8 end

        -- Build buffman table for literal/length codes
        return DecodeUntilEndOfBlock(state, lcodes_huffman_bitlen_counts,
            lcodes_huffman_symbols,
            lcodes_huffman_min_bitlen,
            dcodes_huffman_bitlen_counts,
            dcodes_huffman_symbols, dcodes_huffman_min_bitlen)
    end

    -- Decompress a deflate stream
    -- @param state: a decompression state
    -- @return the decompressed string if succeeds. nil if fails.
    local function Inflate(state)
        local ReadBits = state.ReadBits

        local is_last_block
        while not is_last_block do
            is_last_block = (ReadBits(1) == 1)
            local block_type = ReadBits(2)
            local status
            if block_type == 0 then
                status = DecompressStoreBlock(state)
            elseif block_type == 1 then
                status = DecompressFixBlock(state)
            elseif block_type == 2 then
                status = DecompressDynamicBlock(state)
            else
                return nil, -1 -- invalid block type (type == 3)
            end
            if status ~= 0 then return nil, status end
        end

        state.result_buffer[#state.result_buffer + 1] =
            table.concat(state.buffer, "", 1, state.buffer_size)
        local result = table.concat(state.result_buffer)
        return result
    end

    -- @see LibDeflate:DecompressDeflate(str)
    -- @see LibDeflate:DecompressDeflateWithDict(str, dictionary)
    local function DecompressDeflateInternal(str, dictionary)
        local state = CreateDecompressState(str, dictionary)
        local result, status = Inflate(state)
        if not result then return nil, status end

        local bitlen_left = state.ReaderBitlenLeft()
        local bytelen_left = (bitlen_left - bitlen_left % 8) / 8
        return result, bytelen_left
    end

    -- @see LibDeflate:DecompressZlib(str)
    -- @see LibDeflate:DecompressZlibWithDict(str)
    local function DecompressZlibInternal(str, dictionary)
        local state = CreateDecompressState(str, dictionary)
        local ReadBits = state.ReadBits

        local CMF = ReadBits(8)
        if state.ReaderBitlenLeft() < 0 then
            return nil, 2 -- available inflate data did not terminate
        end
        local CM = CMF % 16
        local CINFO = (CMF - CM) / 16
        if CM ~= 8 then
            return nil, -12 -- invalid compression method
        end
        if CINFO > 7 then
            return nil, -13 -- invalid window size
        end

        local FLG = ReadBits(8)
        if state.ReaderBitlenLeft() < 0 then
            return nil, 2 -- available inflate data did not terminate
        end
        if (CMF * 256 + FLG) % 31 ~= 0 then
            return nil, -14 -- invalid header checksum
        end

        local FDIST = ((FLG - FLG % 32) / 32 % 2)
        local FLEVEL = ((FLG - FLG % 64) / 64 % 4) -- luacheck: ignore FLEVEL

        if FDIST == 1 then
            if not dictionary then
                return nil, -16 -- need dictonary, but dictionary is not provided.
            end
            local byte3 = ReadBits(8)
            local byte2 = ReadBits(8)
            local byte1 = ReadBits(8)
            local byte0 = ReadBits(8)
            local actual_adler32 = byte3 * 16777216 + byte2 * 65536 + byte1 * 256 +
                byte0
            if state.ReaderBitlenLeft() < 0 then
                return nil, 2 -- available inflate data did not terminate
            end
            if not IsEqualAdler32(actual_adler32, dictionary.adler32) then
                return nil, -17 -- dictionary adler32 does not match
            end
        end
        local result, status = Inflate(state)
        if not result then return nil, status end
        state.SkipToByteBoundary()

        local adler_byte0 = ReadBits(8)
        local adler_byte1 = ReadBits(8)
        local adler_byte2 = ReadBits(8)
        local adler_byte3 = ReadBits(8)
        if state.ReaderBitlenLeft() < 0 then
            return nil, 2 -- available inflate data did not terminate
        end

        local adler32_expected = adler_byte0 * 16777216 + adler_byte1 * 65536 +
            adler_byte2 * 256 + adler_byte3
        local adler32_actual = LibDeflate:Adler32(result)
        if not IsEqualAdler32(adler32_expected, adler32_actual) then
            return nil, -15 -- Adler32 checksum does not match
        end

        local bitlen_left = state.ReaderBitlenLeft()
        local bytelen_left = (bitlen_left - bitlen_left % 8) / 8
        return result, bytelen_left
    end

    --- Decompress a raw deflate compressed data.
    -- @param str [string] The data to be decompressed.
    -- @return [string/nil] If the decompression succeeds, return the decompressed
    -- data. If the decompression fails, return nil. You should check if this return
    -- value is non-nil to know if the decompression succeeds.
    -- @return [integer] If the decompression succeeds, return the number of
    -- unprocessed bytes in the input compressed data. This return value is a
    -- positive integer if the input data is a valid compressed data appended by an
    -- arbitary non-empty string. This return value is 0 if the input data does not
    -- contain any extra bytes.<br>
    -- If the decompression fails (The first return value of this function is nil),
    -- this return value is undefined.
    -- @see LibDeflate:CompressDeflate
    function deflate_decompress(str)
        local arg_valid, arg_err = IsValidArguments(str)
        if not arg_valid then
            error(("Usage: LibDeflate:DecompressDeflate(str): " .. arg_err), 2)
        end
        return DecompressDeflateInternal(str)
    end


    --- Decompress a zlib compressed data.
    -- @param str [string] The data to be decompressed
    -- @return [string/nil] If the decompression succeeds, return the decompressed
    -- data. If the decompression fails, return nil. You should check if this return
    -- value is non-nil to know if the decompression succeeds.
    -- @return [integer] If the decompression succeeds, return the number of
    -- unprocessed bytes in the input compressed data. This return value is a
    -- positive integer if the input data is a valid compressed data appended by an
    -- arbitary non-empty string. This return value is 0 if the input data does not
    -- contain any extra bytes.<br>
    -- If the decompression fails (The first return value of this function is nil),
    -- this return value is undefined.
    -- @see LibDeflate:CompressZlib
    function zlib_decompress(str)
        local arg_valid, arg_err = IsValidArguments(str)
        if not arg_valid then
            error(("Usage: LibDeflate:DecompressZlib(str): " .. arg_err), 2)
        end
        return DecompressZlibInternal(str)
    end


    -- Calculate the huffman code of fixed block
    do
        _fix_block_literal_huffman_bitlen = {}
        for sym = 0, 143 do _fix_block_literal_huffman_bitlen[sym] = 8 end
        for sym = 144, 255 do _fix_block_literal_huffman_bitlen[sym] = 9 end
        for sym = 256, 279 do _fix_block_literal_huffman_bitlen[sym] = 7 end
        for sym = 280, 287 do _fix_block_literal_huffman_bitlen[sym] = 8 end

        _fix_block_dist_huffman_bitlen = {}
        for dist = 0, 31 do _fix_block_dist_huffman_bitlen[dist] = 5 end
        local status
        status, _fix_block_literal_huffman_bitlen_count, _fix_block_literal_huffman_to_deflate_code =
            GetHuffmanForDecode(_fix_block_literal_huffman_bitlen, 287, 9)
        assert(status == 0)
        status, _fix_block_dist_huffman_bitlen_count, _fix_block_dist_huffman_to_deflate_code =
            GetHuffmanForDecode(_fix_block_dist_huffman_bitlen, 31, 5)
        assert(status == 0)

        _fix_block_literal_huffman_code = GetHuffmanCodeFromBitlen(
            _fix_block_literal_huffman_bitlen_count,
            _fix_block_literal_huffman_bitlen, 287, 9)
        _fix_block_dist_huffman_code = GetHuffmanCodeFromBitlen(
            _fix_block_dist_huffman_bitlen_count,
            _fix_block_dist_huffman_bitlen, 31, 5)
    end

    -- Prefix encoding algorithm
    -- Credits to LibCompress.
    -- The code has been rewritten by the author of LibDeflate.
    ------------------------------------------------------------------------------

    -- to be able to match any requested byte value, the search
    -- string must be preprocessed characters to escape with %:
    -- ( ) . % + - * ? [ ] ^ $
    -- "illegal" byte values:
    -- 0 is replaces %z
    local _gsub_escape_table = {
        ["\000"] = "%z",
        ["("] = "%(",
        [")"] = "%)",
        ["."] = "%.",
        ["%"] = "%%",
        ["+"] = "%+",
        ["-"] = "%-",
        ["*"] = "%*",
        ["?"] = "%?",
        ["["] = "%[",
        ["]"] = "%]",
        ["^"] = "%^",
        ["$"] = "%$"
    }

    local function escape_for_gsub(str)
        return str:gsub("([%z%(%)%.%%%+%-%*%?%[%]%^%$])", _gsub_escape_table)
    end





    -- Credits to WeakAuras2 and Galmok for the 6 bit encoding algorithm.
    -- The code has been rewritten by the author of LibDeflate.
    -- The result of encoding will be 25% larger than the
    -- origin string, but every single byte of the encoding result will be
    -- printable characters as the following.
    local _byte_to_6bit_char = {
        [0] = "a",
        "b",
        "c",
        "d",
        "e",
        "f",
        "g",
        "h",
        "i",
        "j",
        "k",
        "l",
        "m",
        "n",
        "o",
        "p",
        "q",
        "r",
        "s",
        "t",
        "u",
        "v",
        "w",
        "x",
        "y",
        "z",
        "A",
        "B",
        "C",
        "D",
        "E",
        "F",
        "G",
        "H",
        "I",
        "J",
        "K",
        "L",
        "M",
        "N",
        "O",
        "P",
        "Q",
        "R",
        "S",
        "T",
        "U",
        "V",
        "W",
        "X",
        "Y",
        "Z",
        "0",
        "1",
        "2",
        "3",
        "4",
        "5",
        "6",
        "7",
        "8",
        "9",
        "(",
        ")"
    }

    local _6bit_to_byte = {
        [97] = 0,
        [98] = 1,
        [99] = 2,
        [100] = 3,
        [101] = 4,
        [102] = 5,
        [103] = 6,
        [104] = 7,
        [105] = 8,
        [106] = 9,
        [107] = 10,
        [108] = 11,
        [109] = 12,
        [110] = 13,
        [111] = 14,
        [112] = 15,
        [113] = 16,
        [114] = 17,
        [115] = 18,
        [116] = 19,
        [117] = 20,
        [118] = 21,
        [119] = 22,
        [120] = 23,
        [121] = 24,
        [122] = 25,
        [65] = 26,
        [66] = 27,
        [67] = 28,
        [68] = 29,
        [69] = 30,
        [70] = 31,
        [71] = 32,
        [72] = 33,
        [73] = 34,
        [74] = 35,
        [75] = 36,
        [76] = 37,
        [77] = 38,
        [78] = 39,
        [79] = 40,
        [80] = 41,
        [81] = 42,
        [82] = 43,
        [83] = 44,
        [84] = 45,
        [85] = 46,
        [86] = 47,
        [87] = 48,
        [88] = 49,
        [89] = 50,
        [90] = 51,
        [48] = 52,
        [49] = 53,
        [50] = 54,
        [51] = 55,
        [52] = 56,
        [53] = 57,
        [54] = 58,
        [55] = 59,
        [56] = 60,
        [57] = 61,
        [40] = 62,
        [41] = 63
    }

    --- Encode the string to make it printable. <br>
    --
    -- Credit to WeakAuras2, this function is equivalant to the implementation
    -- it is using right now. <br>
    -- The code has been rewritten by the author of LibDeflate. <br>
    -- The encoded string will be 25% larger than the origin string. However, every
    -- single byte of the encoded string will be one of 64 printable ASCII
    -- characters, which are can be easier copied, pasted and displayed.
    -- (26 lowercase letters, 26 uppercase letters, 10 numbers digits,
    -- left parenthese, or right parenthese)
    -- @param str [string] The string to be encoded.
    -- @return [string] The encoded string.
    function LibDeflate:EncodeForPrint(str)
        if type(str) ~= "string" then
            error(("Usage: LibDeflate:EncodeForPrint(str):" ..
                " 'str' - string expected got '%s'."):format(type(str)), 2)
        end
        local strlen = #str
        local strlenMinus2 = strlen - 2
        local i = 1
        local buffer = {}
        local buffer_size = 0
        while i <= strlenMinus2 do
            local x1, x2, x3 = string.byte(str, i, i + 2)
            i = i + 3
            local cache = x1 + x2 * 256 + x3 * 65536
            local b1 = cache % 64
            cache = (cache - b1) / 64
            local b2 = cache % 64
            cache = (cache - b2) / 64
            local b3 = cache % 64
            local b4 = (cache - b3) / 64
            buffer_size = buffer_size + 1
            buffer[buffer_size] = _byte_to_6bit_char[b1] .. _byte_to_6bit_char[b2] ..
                _byte_to_6bit_char[b3] .. _byte_to_6bit_char[b4]
        end

        local cache = 0
        local cache_bitlen = 0
        while i <= strlen do
            local x = string.byte(str, i, i)
            cache = cache + x * _pow2[cache_bitlen]
            cache_bitlen = cache_bitlen + 8
            i = i + 1
        end
        while cache_bitlen > 0 do
            local bit6 = cache % 64
            buffer_size = buffer_size + 1
            buffer[buffer_size] = _byte_to_6bit_char[bit6]
            cache = (cache - bit6) / 64
            cache_bitlen = cache_bitlen - 6
        end

        return table.concat(buffer)
    end

    --- Decode the printable string produced by LibDeflate:EncodeForPrint.
    -- "str" will have its prefixed and trailing control characters or space
    -- removed before it is decoded, so it is easier to use if "str" comes form
    -- user copy and paste with some prefixed or trailing spaces.
    -- Then decode fails if the string contains any characters cant be produced by
    -- LibDeflate:EncodeForPrint. That means, decode fails if the string contains a
    -- characters NOT one of 26 lowercase letters, 26 uppercase letters,
    -- 10 numbers digits, left parenthese, or right parenthese.
    -- @param str [string] The string to be decoded
    -- @return [string/nil] The decoded string if succeeds. nil if fails.
    function LibDeflate:DecodeForPrint(str)
        if type(str) ~= "string" then
            error(("Usage: LibDeflate:DecodeForPrint(str):" ..
                " 'str' - string expected got '%s'."):format(type(str)), 2)
        end
        str = str:gsub("^[%c ]+", "")
        str = str:gsub("[%c ]+$", "")

        local strlen = #str
        if strlen == 1 then return nil end
        local strlenMinus3 = strlen - 3
        local i = 1
        local buffer = {}
        local buffer_size = 0
        while i <= strlenMinus3 do
            local x1, x2, x3, x4 = string.byte(str, i, i + 3)
            x1 = _6bit_to_byte[x1]
            x2 = _6bit_to_byte[x2]
            x3 = _6bit_to_byte[x3]
            x4 = _6bit_to_byte[x4]
            if not (x1 and x2 and x3 and x4) then return nil end
            i = i + 4
            local cache = x1 + x2 * 64 + x3 * 4096 + x4 * 262144
            local b1 = cache % 256
            cache = (cache - b1) / 256
            local b2 = cache % 256
            local b3 = (cache - b2) / 256
            buffer_size = buffer_size + 1
            buffer[buffer_size] = _byte_to_char[b1] .. _byte_to_char[b2] ..
                _byte_to_char[b3]
        end

        local cache = 0
        local cache_bitlen = 0
        while i <= strlen do
            local x = string.byte(str, i, i)
            x = _6bit_to_byte[x]
            if not x then return nil end
            cache = cache + x * _pow2[cache_bitlen]
            cache_bitlen = cache_bitlen + 6
            i = i + 1
        end

        while cache_bitlen >= 8 do
            local byte = cache % 256
            buffer_size = buffer_size + 1
            buffer[buffer_size] = _byte_to_char[byte]
            cache = (cache - byte) / 256
            cache_bitlen = cache_bitlen - 8
        end

        return table.concat(buffer)
    end



    -- For test. Don't use the functions in this table for real application.
    -- Stuffs in this table is subject to change.
    LibDeflate.internals = {
        LoadStringToTable = LoadStringToTable,
        IsEqualAdler32 = IsEqualAdler32,
        _byte_to_6bit_char = _byte_to_6bit_char,
        _6bit_to_byte = _6bit_to_byte,
    }

--[[-- Commandline options
@class table
@name CommandlineOptions
@usage lua LibDeflate.lua [OPTION] [INPUT] [OUTPUT]
\-0    store only. no compression.
\-1    fastest compression.
\-9    slowest and best compression.
\-d    do decompression instead of compression.
\--dict <filename> specify the file that contains
the entire preset dictionary.
\-h    give this help.
\--strategy <fixed/huffman_only/dynamic> specify a special compression strategy.
\-v    print the version and copyright info.
\--zlib  use zlib format instead of raw deflate.
]]

    -- currently no plan to support stdin and stdout.
    -- Because Lua in Windows does not set stdout with binary mode.


    return LibDeflate
end

function RoCrypt.compression.zlib()
    return {
        compress = (function(str)
            if zlib_decompress then
                return zlib_compress(str)
            else 
                libdeflate_bootstrapper()
                return zlib_compress(str)
            end
        end),
        decompress = (function(str)
            if zlib_decompress then
                return zlib_decompress(str)
            else 
                libdeflate_bootstrapper()
                return zlib_decompress(str)
            end
        end)
    }
end

function RoCrypt.compression.deflate()
    return {
        compress = (function(str)
            if deflate_decompress then
                return deflate_compress(str)
            else 
                libdeflate_bootstrapper()
                return deflate_compress(str)
            end
        end),
        decompress = (function(str)
            if deflate_decompress then
                return deflate_decompress(str)
            else 
                libdeflate_bootstrapper()
                return deflate_decompress(str)
            end
        end)
    }
end


return RoCrypt



