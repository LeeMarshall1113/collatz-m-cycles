import Collatz.MCycle109Certs43

/-!
# Certificates of the listed shapes of `data109`, chunks 172..175
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_172 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_172 = true := by
  decide +kernel

theorem certs109_173 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_173 = true := by
  decide +kernel

theorem certs109_174 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_174 = true := by
  decide +kernel

theorem certs109_175 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_175 = true := by
  decide +kernel

end Collatz
