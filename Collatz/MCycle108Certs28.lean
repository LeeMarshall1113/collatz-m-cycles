import Collatz.MCycle108Certs27

/-!
# Certificates of the listed shapes of `data108`, chunks 108..111
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_108 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_108 = true := by
  decide +kernel

theorem certs108_109 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_109 = true := by
  decide +kernel

theorem certs108_110 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_110 = true := by
  decide +kernel

theorem certs108_111 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_111 = true := by
  decide +kernel

end Collatz
