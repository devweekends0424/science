# P vs NP 計算実験および数理ノート（敵対的監査反映版）

本ディレクトリは、P vs NP に関する実験記録および数理的定式化について、敵対的監査（Adversarial Audit）で判明した限界・反証箇所を明確に分離してまとめた公開用ノートです。

## 1. 実験結果サマリー（サウロンRPG・攻略本モデル）

### A. 固定ビット助言 vs 構造ルール助言（Planted 3-SAT, $\alpha = 4.26$, 各30体）
* **固定ビット助言 (`pnp_rpg_strategy_guide`)**:
  * 正解ビットを $k$ ビット渡すことで探索ノード数は減少するが、これは計算コストの「問題解読（探索）」から「攻略本作成（外部前計算）」への移転に過ぎず、計算量クラスとしては非一様計算量 $P/\mathrm{poly}$ に留まる（Karp–Lipton の定理により $\Sigma_2^P = \Pi_2^P$ は導けても $P=NP$ にはならない）。
* **構造ルール助言 (`pnp_rpg_structural_guide`, $k=4$ bits)**:
  * $n=16, m=68$: 助言なし `18.30` → 4bit構造多数決 `3.43`（参考: 4bitオラクル `5.30`）
  * $n=20, m=85$: 助言なし `22.93` → 4bit構造多数決 `5.87`（参考: 4bitオラクル `7.60`）
  * **対照実験（Random 3-SAT & 3-XOR-SAT, `run_advice_efficiency.py` / `run_xorsat_resilience.py`）**:
    * Random 3-SAT ($n=16$): 構造多数決は `4.02%` 削減（`0.0148 bit/bit`）に低下。
    * 3-XOR-SAT ($n=14, 16$): 構造多数決は **`-8.67%` / `-10.35%`（無力・逆効果）**。
    * 結論: Planted 分布の極性バイアスが消える一般分布・XOR構造では、局所的統計ルールによる探索削減は成立しない（Advice-Resilient Hardness）。

### B. Lean 4.35.0 形式検証 (`AdviceResilience.lean`)
* `pnpAdv_syntax_non_invariance`: 重複節追加による $Z_\varphi(z)$ の構文非不変性を証明（`sorry` なし）。
* `pnpAdv_advice_pigeonhole_bound`: $k < n$ の固定助言ビットでは $2^n$ 通りの解空間を覆えないことを鳩の巣原理から証明（`sorry` なし）。

---

## 2. 敵対的監査により明確化された数理的限界

1. **分配関数 $Z_\varphi(z) = \sum_{y \in \{0,1\}^n} z^{E_\varphi(y)}$ の構文依存性**:
   * $Z_\varphi(z)$ はブール関数の不変量ではなく CNF の表現（重複節など）に依存する。
   * $Z_\varphi(0) = \#\mathrm{SAT}(\varphi)$ 自体が $\#P$-完全であるため、$Z_\varphi(z)$ の係数や複素零点の厳密構成は $NP$ より困難。
2. **量子振幅 $A_\varphi(\theta) = \mathbb{E}_{y \sim U}[e^{i\theta E_\varphi(y)}]$ のノイズ床**:
   * モンテカルロ推定の標準誤差は $O(1/\sqrt{N_s})$ であるのに対し、ハードなインスタンスの信号強度は $2^{-\Omega(n)}$ となり、指数的サンプル数 $N_s = \Omega(2^{2n})$ を要する。
3. **ガロア群 $\mathrm{Gal}(Z_\varphi / \mathbb{Q})$ の非弁別性**:
   * 多項式のガロア群は違反節数ごとの個数 $c_k$ にのみ依存し、割当て空間 $\{0,1\}^n$ の論理的対称性とは独立。また $1+z^m$ のように可換群 $(\mathbb{Z}/2m\mathbb{Z})^\times$ になる反例が存在する。
4. **$VP \ne VNP$ と $P \ne NP$ の分離**:
   * オリジナルノート（Turn 45, 50）で導入された多項式族 $\{F_n(X,z)\}_{n \ge 1} \in \mathrm{VNP}$ は定義からの帰結であり、$F_n \notin \mathrm{VP}$ を示すものではありません。
   * また、標数0の体上の代数的複雑性の分離（$VP \ne VNP$）からブール回路の分離（$P \ne NP$）は直接導かれません。
5. **違反節数エントロピー $H(E_\varphi) = -\sum_{k=0}^m p_k \log_2 p_k$**:
   * $p_k = c_k / 2^n$ の厳密計算自体が $\#P$-hard であるため、SAT 判定の高速化には直接使えません。
