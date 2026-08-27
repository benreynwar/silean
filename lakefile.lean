import Lake

open Lake DSL

package «silean2» where

@[default_target]
lean_lib «Silean2» where

@[default_target]
lean_lib «Silean2Examples» where
  roots := #[`Silean2Examples]

lean_exe «emit-bit-register» where
  root := `Silean2.Emitters.BitRegister

lean_exe «emit-structured-fifo» where
  root := `Silean2.Emitters.StructuredFifo

lean_exe «emit-pointer-fifo» where
  root := `Silean2.Emitters.PointerFifo

lean_exe «emit-bit-register-bank» where
  root := `Silean2.Emitters.BitRegisterBank
