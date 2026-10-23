import Collatz.MCycle109Certs40

/-!
# Certificates of the listed shapes of `data109`, chunks 160..163
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_160 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_160 = true := by
  decide +kernel

theorem certs109_161 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_161 = true := by
  decide +kernel

theorem certs109_162 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_162 = true := by
  decide +kernel

theorem certs109_163 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_163 = true := by
  decide +kernel

end Collatz
