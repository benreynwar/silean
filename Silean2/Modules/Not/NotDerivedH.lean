import Silean2.FoundationsH
import Silean2.Modules.Not.NotH
import Silean2.Modules.Not.Internals.CertValidA

namespace Silean2.Modules.Not

open Silean2.Foundations
open Silean2.Modules.Not.Internals

def notFromNandCert : ModuleBodyCert notFromNand := {
  spec := notSpec
  childSpecs := fun _ => Nand.nandSpec
  valid := notFromNandCertValid
}

end Silean2.Modules.Not
