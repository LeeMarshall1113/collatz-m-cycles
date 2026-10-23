import Collatz.MCycle108Certs26

/-!
# Certificates of the listed shapes of `data108`, chunks 104..107
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_104 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_104 = true := by
  decide +kernel

theorem certs108_105 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_105 = true := by
  decide +kernel

theorem certs108_106 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_106 = true := by
  decide +kernel

theorem certs108_107 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_107 = true := by
  decide +kernel

end Collatz
