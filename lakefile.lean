import Lake

open Lake DSL

package «silean» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib «Silean» where

@[default_target]
lean_lib «HTFFT» where

@[default_target]
lean_lib «SileanTests» where
  srcDir := "tests/silean/lean"
  roots := #[`SileanTests]

@[default_target]
lean_lib «HTFFTTests» where
  srcDir := "tests/htfft/lean"
  roots := #[`HTFFTTests]

lean_exe «emit-bit-register» where
  root := `Silean.Emitters.BitRegister

lean_exe «emit-structured-fifo» where
  root := `Silean.Emitters.StructuredFifo

lean_exe «emit-pointer-fifo» where
  root := `Silean.Emitters.PointerFifo

lean_exe «emit-serial-fifo» where
  root := `Silean.Emitters.SerialFifo

lean_exe «emit-bit-register-bank» where
  root := `Silean.Emitters.BitRegisterBank
