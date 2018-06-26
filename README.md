# Idris WebAssembly CodeGen

*It is still on early stages of development.*

## Implemented
  * [x] Control flow instructions
  * [x] Garbadge Collection
  * [x] String representation and implementation of primitive operations in RTS(with UTF8 support)
  * [x] Char and native int operations
  * [x] Double operations
  * [x] Bit8/16/32/64 operations
  * [x] Convertions (int to big num, bits to int, etc)
  * [x] Unwrap self-tail calls with LOOP instruction
  * [x] Effective unboxed representation for int and char
  * [x] Effective substrings representation as StrOffset

## Todo
  * [ ] BigNum primitives(now they are emulated as WASM i64 number)
  * [ ] Pass Idris language test suite
  * [ ] FFI and Idris-level support for new back-end

## Build
Current implementation fully depends on [haskell-wasm](https://github.com/SPY/haskell-wasm).
To build you need clone [idris-codegen-wasm](https://github.com/SPY/idris-codegen-wasm)

```
cd ./idris-codegen-wasm && cabal build
```

Sample code fully functioning now

```
module Main

factorial : Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)

range : Int -> Int -> List Int
range from to = if from == to then [to] else from :: range (from + 1) to

moreThan : Int -> Int -> Maybe Int
moreThan lowLimit n = if n >= lowLimit then Just n else Nothing

main : IO ()
main = do
    let hello = "Hello"
    let world = "Мир"
    -- long string to trigger GC
    let longString = "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum."
    putStrLn $ show $ range 1 10
    putStrLn $ show $ split (== ' ') longString
    putStrLn $ hello ++ strCons ' ' world
    putStrLn $ show $ sum $ range 0 256
    putStrLn $ show $ fromMaybe 42 $ moreThan 88 $ factorial 5
```

To build it run:
```
idris fact.idr --codegen wasm -o fact.wasm
```

For running compiled code you can use runner from `rts/index.html`. It contains some bootstrap code and simple tools for runtime introspection(print const section, stack, heap, fallback GC implementation, etc).