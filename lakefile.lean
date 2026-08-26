import Lake

open Lake DSL

package «silean2» where

@[default_target]
lean_lib «Silean2» where

@[default_target]
lean_lib «Silean2Examples» where
  roots := #[`Silean2Examples]
