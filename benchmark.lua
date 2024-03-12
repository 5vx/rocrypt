local RoCrypt = require(script.Parent) or require(script.RoCrypt) or require(script.Parent.RoCrypt)

local function benchmarkFunction(funcName, func, iterations, ...)
    local args = {...}
    local totalTime = 0
    local startTime, endTime

    for i = 1, iterations do
        startTime = os.clock()
        func(unpack(args))
        endTime = os.clock()
        totalTime = totalTime + (endTime - startTime)
    end

    local averageTime = totalTime / iterations
    return totalTime, averageTime, iterations
end

local iterations = 1000
local results = {}

for i, v in pairs(RoCrypt) do
    if type(v) == "function" and v ~= RoCrypt.hmac and not string.find(i, "shake") then
        local totalTime, averageTime, iterations = benchmarkFunction(i, v, iterations, "Hello, World!")
        table.insert(results, {
            name = i,
            totalTime = totalTime,
            averageTime = averageTime,
            iterations = iterations
        })
    end
end

table.sort(results, function(a, b)
    return a.totalTime > b.totalTime
end)

for _, result in ipairs(results) do
    print(string.format("[%s] took %.6f seconds to complete %d iterations with an average of %.6f seconds", result.name, result.totalTime, result.iterations, result.averageTime))
end