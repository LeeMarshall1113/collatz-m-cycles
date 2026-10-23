import Collatz.MCycle109Certs46

/-!
# Certificates of the listed shapes of `data109`, chunks 184..187
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_184 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_184 = true := by
  decide +kernel

theorem certs109_185 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_185 = true := by
  decide +kernel

theorem certs109_186 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_186 = true := by
  decide +kernel

theorem certs109_187 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_187 = true := by
  decide +kernel

end Collatz
