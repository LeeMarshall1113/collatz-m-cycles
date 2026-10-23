import Collatz.MCycle109Certs41

/-!
# Certificates of the listed shapes of `data109`, chunks 164..167
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_164 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_164 = true := by
  decide +kernel

theorem certs109_165 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_165 = true := by
  decide +kernel

theorem certs109_166 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_166 = true := by
  decide +kernel

theorem certs109_167 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_167 = true := by
  decide +kernel

end Collatz
