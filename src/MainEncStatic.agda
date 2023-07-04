open import Prelude

open import IO
open import AsciiStatic

main : IO ⊤
main = do
  hSetEncoding stdin char8
  hSetEncoding stdout char8
  cs <- readAscii
  let bs = asciiEnc cs
  writeBytes bs
  exitWith Success
