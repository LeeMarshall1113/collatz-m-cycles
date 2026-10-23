import Collatz.MCycle109Certs23

/-!
# Certificates of the listed shapes of `data109`, chunks 92..95
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_92 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_92 = true := by
  decide +kernel

theorem certs109_93 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_93 = true := by
  decide +kernel

theorem certs109_94 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_94 = true := by
  decide +kernel

theorem certs109_95 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_95 = true := by
  decide +kernel

end Collatz
