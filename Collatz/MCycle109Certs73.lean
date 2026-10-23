import Collatz.MCycle109Certs72

/-!
# Certificates of the listed shapes of `data109`, chunks 288..291
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_288 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_288 = true := by
  decide +kernel

theorem certs109_289 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_289 = true := by
  decide +kernel

theorem certs109_290 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_290 = true := by
  decide +kernel

theorem certs109_291 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_291 = true := by
  decide +kernel

end Collatz
