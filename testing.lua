local RoCrypt = require(script.Parent) or require(script.RoCrypt) or require(script.Parent.RoCrypt)
local expected = {
    ["sha224"] =   {
        RoCrypt.sha224,
        "The quick brown fox jumps over the lazy dog",
        "730e109bd7a8a32b1cb9d9a09aa2325d2430587ddbc0c38bad911525"
    },
    ["sha256"] =   {
        RoCrypt.sha256,
        "The quick brown fox jumps over the lazy dog",
        "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592"
    },
    ["sha384"] =    {
        RoCrypt.sha384,
        "The quick brown fox jumps over the lazy dog",
        "ca737f1014a48f4c0b6dd43cb177b0afd9e5169367544c494011e3317dbf9a509cb1e5dc1e85a941bbee3d7f2afbc9b1"
    },
    ["sha512"] = {
        RoCrypt.sha512,
        "The quick brown fox jumps over the lazy dog",
        "07e547d9586f6a73f73fbac0435ed76951218fb7d0c8d788a309d785436bbb642e93a252a954f23912547d1e8a3b5ed6e1bfd7097821233fa0538f3db854fee6"
    },
    ["sha3_224"] = {
        RoCrypt.sha3_224,
        "The quick brown fox jumps over the lazy dog",
        "d15dadceaa4d5d7bb3b48f446421d542e08ad8887305e28d58335795"
    },
    ["sha3_256"] = {
        RoCrypt.sha3_256,
        "The quick brown fox jumps over the lazy dog",
        "69070dda01975c8c120c3aada1b282394e7f032fa9cf32f4cb2259a0897dfc04"
    },
    ["sha3_384"] = {
        RoCrypt.sha3_384,
        "The quick brown fox jumps over the lazy dog",
        "7063465e08a93bce31cd89d2e3ca8f602498696e253592ed26f07bf7e703cf328581e1471a7ba7ab119b1a9ebdf8be41"
    },
    ["sha3_512"] = {
        RoCrypt.sha3_512,
        "The quick brown fox jumps over the lazy dog",
        "01dedd5de4ef14642445ba5f5b97c15e47b9ad931326e4b0727cd94cefc44fff23f07bf543139939b49128caf436dc1bdee54fcb24023a08d9403f9b4bf0d450"
    },
    ["md2"] = {
        RoCrypt.md2,
        "The quick brown fox jumps over the lazy dog",
        "03d85a0d629d2c442e987525319fc471"
    },
    ["md4"] = {
        RoCrypt.md4,
        "The quick brown fox jumps over the lazy dog",
        "1bee69a46ba811185c194762abaeae90"
    },
    ["md5"] = {
        RoCrypt.md5,
        "The quick brown fox jumps over the lazy dog",
        "9e107d9d372bb6826bd81d3542a419d6"
    },
    ["ripemd128"] = {
        RoCrypt.ripemd128,
        "The quick brown fox jumps over the lazy dog",
        "3fa9b57f053c053fbe2735b2380db596"
    },
    ["ripemd160"] = {
        RoCrypt.ripemd160,
        "The quick brown fox jumps over the lazy dog",
        "37f332f68db77bd9d7edd4969571ad671cf9dd3b"
    },
    ["crc32"] = {
        RoCrypt.crc32,
        "The quick brown fox jumps over the lazy dog",
        1095738169
    },
    ["base64"] = {
        RoCrypt.base64().encode,
        "The quick brown fox jumps over the lazy dog",
        "VGhlIHF1aWNrIGJyb3duIGZveCBqdW1wcyBvdmVyIHRoZSBsYXp5IGRvZw=="
    },
    ["base91"] = {
        RoCrypt.base91().encode,
        "The quick brown fox jumps over the lazy dog",
        "nX^Iz?T1s!2t:aRn#o>vf>6C9#`##mlLK#_1:Wzv;RG!,a%q3Lc=Z"
    },

}
for i,v in pairs(expected) do 
    output = v[1](v[2])
    if output == v[3] then
        print( i ..  "'s output of \"".. v[2] .."\" is accurate")
    else 
        warn("the ".. i .. " output of \"" .. v[2] .. "\" is invalid -- return was " ..  output .. " instead of " .. v[3])
    end
end