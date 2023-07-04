open import Prelude hiding (Fin)
open import Tactic.Nat

open import Range
open import Ascii


postulate
  isEOF : IO Bool
  Handle : Set
  TextEncoding : Set
  hSetEncoding : Handle -> TextEncoding -> IO Unit
  char8 : TextEncoding
  stdin : Handle
  stdout : Handle
  localeEncoding : TextEncoding

{-# FOREIGN GHC import qualified System.IO #-}
{-# COMPILE GHC isEOF = System.IO.isEOF #-}
{-# COMPILE GHC Handle = type System.IO.Handle #-}
{-# COMPILE GHC TextEncoding = type System.IO.TextEncoding #-}
{-# COMPILE GHC hSetEncoding = System.IO.hSetEncoding #-}
{-# COMPILE GHC char8 = System.IO.char8 #-}
{-# COMPILE GHC localeEncoding = System.IO.localeEncoding #-}
{-# COMPILE GHC stdin = System.IO.stdin #-}
{-# COMPILE GHC stdout = System.IO.stdout #-}

{-# TERMINATING #-}
readAscii : IO (List Ascii)
readAscii = do
  done ← isEOF
  if done then pure [] else do
    (just c) ← charToAscii <$> getChar
      where nothing → exitWith (Failure 1)
    cs ← readAscii
    pure $ c ∷ cs

writeAscii : List Ascii → IO ⊤
writeAscii []       = pure unit
writeAscii (c ∷ cs) = putChar (asciiToChar c) >> writeAscii cs

{-# TERMINATING #-}
readBytes : IO (List Byte)
readBytes = do
  done ← isEOF
  if done then pure [] else do
    (just c) ← charToByte <$> getChar
      where nothing → exitWith (Failure 1)
    cs ← readBytes
    pure $ c ∷ cs

writeBytes : List Byte → IO ⊤
writeBytes []       = pure unit
writeBytes (c ∷ cs) = putChar (byteToChar c) >> writeBytes cs

