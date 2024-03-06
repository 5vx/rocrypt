# RoCrypt

## Description
A pure-Lua (5.1) cryptography module supporting:
- Functions to calculate SHA digest
  - SHA-256
  - SHA-512
- Cyclic redundancy checks (CRC) algorithms
  - CRC32
- And asymmetric algorithms
  - RSA

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