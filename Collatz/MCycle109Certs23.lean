import Collatz.MCycle109Certs22

/-!
# Certificates of the listed shapes of `data109`, chunks 88..91
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_88 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_88 = true := by
  decide +kernel

theorem certs109_89 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_89 = true := by
  decide +kernel

theorem certs109_90 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_90 = true := by
  decide +kernel

theorem certs109_91 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_91 = true := by
  decide +kernel

end Collatz
