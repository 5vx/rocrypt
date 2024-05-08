# RoCrypt

## Description
A pure-Lua (5.1) cryptography module supporting:
- Cryptographic hash functions (CHF)
  - MD2, MD4, MD5
  - RIPEMD-128, RIPEMD-160
  - SHA1, SHA-224, SHA-256, SHA-384, SHA-512
  - SHA3-224, SHA3-256, SHA3-384, SHA3-512
  - SHAKE128, SHAKE256
- Cyclic redundancy checks (CRC) algorithms
  - CRC32
- Binary-to-hex encoding algorithms
  - Base64, Base91
- Asymmetric algorithms
  - RSA
- Symmetric algorithms
  - AES
  - DES, Triple DES
- Shared-secret algorithms
  - HMAC
- Compression algorithms
  - LZ4, ZLIB, Deflate
- UID (unique identifier) algorithms
  - Snowflake, Sqids

## Credit
- RobloxGamerPro200007 - RSA function
- Egor-Skriptunoff - Creating the original SHA-2 & Keccak (SHA-3) backbones

## Usage

- SHA256
```lua
local RoCrypt = require(script.RoCrypt)
local hash = RoCrypt.sha256("Hello, World!")
```

- RSA
```lua
local RoCrypt = require(script.RoCrypt)
local RSA = RoCrypt.rsa()
n, e, d = RSA.newKeys()
encrypted = RSA.crypt(n, 242351, e)
decrypted = RSA.crypt(n, encrypted, d)
print(decrypted[1]) -- Expected output: 242351
```

- DES3
```lua
local DES3 = RoCrypt.des3()

-- define 8 byte key and plaintext
local key = "secret_k"
local plaintext = "Hello World"

-- convert strings to byte arrays
local keyBytes = {string.byte(key, 1, #key)}
local plaintextBytes = {string.byte(plaintext, 1, #plaintext)}

-- encrypt the plaintext
local ciphertextBytes = DES3.encrypt(keyBytes, plaintextBytes)

-- convert the ciphertext bytes back to a string
local ciphertext = ciphertextBytes
print("Ciphertext: ", ciphertext)

-- decrypt the ciphertext
local decryptedBytes = DES3.decrypt(keyBytes, ciphertextBytes)

-- convert the decrypted bytes back to a string
local decrypted = string.char(unpack(decryptedBytes))
print("Decrypted: " .. decrypted)
```

- Sqids
```lua
local RoCrypt = require(script.Parent.Script.RoCrypt)

local sqids = RoCrypt.sqids().new() --> function
local encoded = sqids:encode(1, 2, 3, 4) --> string: v2fWhzi1
local decoded = sqids:decode(encoded) --> table: {1, 2, 3, 4}
```