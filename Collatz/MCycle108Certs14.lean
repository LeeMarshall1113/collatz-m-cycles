import Collatz.MCycle108Certs13

/-!
# Certificates of the listed shapes of `data108`, chunks 52..55
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_52 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_52 = true := by
  decide +kernel

theorem certs108_53 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_53 = true := by
  decide +kernel

theorem certs108_54 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_54 = true := by
  decide +kernel

theorem certs108_55 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_55 = true := by
  decide +kernel

end Collatz
