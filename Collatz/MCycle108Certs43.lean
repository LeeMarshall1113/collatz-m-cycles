import Collatz.MCycle108Certs42

/-!
# Certificates of the listed shapes of `data108`, chunks 168..171
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_168 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_168 = true := by
  decide +kernel

theorem certs108_169 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_169 = true := by
  decide +kernel

theorem certs108_170 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_170 = true := by
  decide +kernel

theorem certs108_171 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_171 = true := by
  decide +kernel

end Collatz
