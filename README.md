# RoCrypt

## Description
A pure-Lua (5.1) module with the following functions:
- SHA-256
- SHA-512
- CRC32

## Usage
Input data should be a string. Result (SHA digest) is returned in hexadecimal representation as a string of lowercase hex digits.

```lua
local RoCrypt = require(script.RoCrypt)
local hash = RoCrypt.sha256("Hello, World!")
```
