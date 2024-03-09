# RoCrypt

## Description
A pure-Lua (5.1) cryptography module supporting:
- Cryptographic hash functions (CHF)
  - MD4, MD5
  - RIPEMD-160
  - SHA-224, SHA-256, SHA-384, SHA-512
- Cyclic redundancy checks (CRC) algorithms
  - CRC32
- Binary-to-hex encoding algorithms
  - Base64, Base91
- Asymmetric algorithms
  - RSA
- Symmetric algorithms
  - AES
- Shared-secret algorithms
  - HMAC
- UID (unique identifier) algorithms
  - Snowflake

## Credit
- RobloxGamerPro200007 - RSA function
- Egor-Skriptunoff - Creating the original SHA backbone

## Usage
Input data should be a string. Result (SHA digest) is returned in hexadecimal representation as a string of lowercase hex digits.


```lua
local RoCrypt = require(script.RoCrypt)
local hash = RoCrypt.sha256("Hello, World!")
```

```lua
local RoCrypt = require(script.RoCrypt)
local RSA = RoCrypt.rsa()
n, e, d = RSA.newKeys()
encrypted = RSA.crypt(n, 242351, e)
decrypted = RSA.crypt(n, encrypted, d)
print(decrypted[1]) -- Expected output: 242351
```