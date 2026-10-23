import Collatz.MCycle109Certs52

/-!
# Certificates of the listed shapes of `data109`, chunks 208..211
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_208 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_208 = true := by
  decide +kernel

theorem certs109_209 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_209 = true := by
  decide +kernel

theorem certs109_210 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_210 = true := by
  decide +kernel

theorem certs109_211 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_211 = true := by
  decide +kernel

end Collatz
