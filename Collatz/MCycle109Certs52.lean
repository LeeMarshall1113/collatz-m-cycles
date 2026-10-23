import Collatz.MCycle109Certs51

/-!
# Certificates of the listed shapes of `data109`, chunks 204..207
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_204 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_204 = true := by
  decide +kernel

theorem certs109_205 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_205 = true := by
  decide +kernel

theorem certs109_206 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_206 = true := by
  decide +kernel

theorem certs109_207 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_207 = true := by
  decide +kernel

end Collatz
