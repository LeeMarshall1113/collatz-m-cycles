import Collatz.MCycle109Certs42

/-!
# Certificates of the listed shapes of `data109`, chunks 168..171
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_168 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_168 = true := by
  decide +kernel

theorem certs109_169 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_169 = true := by
  decide +kernel

theorem certs109_170 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_170 = true := by
  decide +kernel

theorem certs109_171 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_171 = true := by
  decide +kernel

end Collatz
