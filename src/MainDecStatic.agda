open import Prelude

open import IO
open import AsciiStatic

main : IO ⊤
main = do
  hSetEncoding stdin char8
  hSetEncoding stdout char8
  (just cs) ← asciiDec <$> readBytes
    where nothing → exitWith (Failure 1)
  writeAscii cs
  exitWith Success
