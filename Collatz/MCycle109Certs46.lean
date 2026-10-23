import Collatz.MCycle109Certs45

/-!
# Certificates of the listed shapes of `data109`, chunks 180..183
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_180 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_180 = true := by
  decide +kernel

theorem certs109_181 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_181 = true := by
  decide +kernel

theorem certs109_182 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_182 = true := by
  decide +kernel

theorem certs109_183 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_183 = true := by
  decide +kernel

end Collatz
