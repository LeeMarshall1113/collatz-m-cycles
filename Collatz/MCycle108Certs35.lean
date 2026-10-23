import Collatz.MCycle108Certs34

/-!
# Certificates of the listed shapes of `data108`, chunks 136..139
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_136 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_136 = true := by
  decide +kernel

theorem certs108_137 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_137 = true := by
  decide +kernel

theorem certs108_138 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_138 = true := by
  decide +kernel

theorem certs108_139 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_139 = true := by
  decide +kernel

end Collatz
