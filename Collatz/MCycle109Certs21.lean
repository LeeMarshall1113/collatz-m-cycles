import Collatz.MCycle109Certs20

/-!
# Certificates of the listed shapes of `data109`, chunks 80..83
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_80 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_80 = true := by
  decide +kernel

theorem certs109_81 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_81 = true := by
  decide +kernel

theorem certs109_82 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_82 = true := by
  decide +kernel

theorem certs109_83 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_83 = true := by
  decide +kernel

end Collatz
