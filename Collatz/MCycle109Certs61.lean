import Collatz.MCycle109Certs60

/-!
# Certificates of the listed shapes of `data109`, chunks 240..243
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_240 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_240 = true := by
  decide +kernel

theorem certs109_241 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_241 = true := by
  decide +kernel

theorem certs109_242 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_242 = true := by
  decide +kernel

theorem certs109_243 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_243 = true := by
  decide +kernel

end Collatz
