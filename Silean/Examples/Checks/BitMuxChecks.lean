import Silean.Modules.BitMux

namespace Silean.Examples.Checks.BitMux

open Silean

example : Modules.BitMux.instances.names.values =
    [Modules.BitMux.Instance.invertSelect, Modules.BitMux.Instance.chooseFalse,
      Modules.BitMux.Instance.chooseTrue, Modules.BitMux.Instance.combine] := rfl

example : Modules.BitMux.wiring.moduleOutput .result =
    Modules.BitMux.context.instanceOutput .combine .output := rfl

example : Modules.BitMux.wiring.instanceInput .invertSelect .input =
    Modules.BitMux.context.moduleInput .select := rfl

example : Modules.BitMux.wiring.instanceInput .chooseFalse .left =
    Modules.BitMux.context.moduleInput .whenFalse := rfl

example : Modules.BitMux.wiring.instanceInput .chooseFalse .right =
    Modules.BitMux.context.instanceOutput .invertSelect .output := rfl

example : Modules.BitMux.wiring.instanceInput .chooseTrue .left =
    Modules.BitMux.context.moduleInput .whenTrue := rfl

example : Modules.BitMux.wiring.instanceInput .chooseTrue .right =
    Modules.BitMux.context.moduleInput .select := rfl

example : Modules.BitMux.wiring.instanceInput .combine .left =
    Modules.BitMux.context.instanceOutput .chooseFalse .output := rfl

example : Modules.BitMux.wiring.instanceInput .combine .right =
    Modules.BitMux.context.instanceOutput .chooseTrue .output := rfl

example : Modules.BitMux.wiring.instanceInput .invertSelect .input =
    Modules.BitMux.wiring.instanceInput .chooseTrue .right := rfl

end Silean.Examples.Checks.BitMux
