import Collatz.MCycle109Certs53

/-!
# Certificates of the listed shapes of `data109`, chunks 212..215
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_212 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_212 = true := by
  decide +kernel

theorem certs109_213 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_213 = true := by
  decide +kernel

theorem certs109_214 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_214 = true := by
  decide +kernel

theorem certs109_215 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_215 = true := by
  decide +kernel

end Collatz
