import Collatz.MCycle109Certs30

/-!
# Certificates of the listed shapes of `data109`, chunks 120..123
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_120 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_120 = true := by
  decide +kernel

theorem certs109_121 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_121 = true := by
  decide +kernel

theorem certs109_122 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_122 = true := by
  decide +kernel

theorem certs109_123 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_123 = true := by
  decide +kernel

end Collatz
