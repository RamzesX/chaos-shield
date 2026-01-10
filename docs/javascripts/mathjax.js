/**
 * MathJax Configuration for Omega-Theory
 * Optimized for physics papers with extensive LaTeX
 */

window.MathJax = {
  tex: {
    // Inline and display math delimiters
    inlineMath: [["\\(", "\\)"], ["$", "$"]],
    displayMath: [["\\[", "\\]"], ["$$", "$$"]],

    // Process escapes and environments
    processEscapes: true,
    processEnvironments: true,
    processRefs: true,

    // AMS packages for advanced math
    packages: { '[+]': ['ams', 'newcommand', 'configmacros', 'action', 'physics'] },

    // Custom macros for Omega-Theory
    macros: {
      // Greek letters
      ell: '\\ell',

      // Operators
      Tr: '\\operatorname{Tr}',
      tr: '\\operatorname{tr}',
      det: '\\operatorname{det}',
      sgn: '\\operatorname{sgn}',
      diag: '\\operatorname{diag}',
      Ric: '\\operatorname{Ric}',
      Rm: '\\operatorname{Rm}',
      Vol: '\\operatorname{Vol}',

      // Derivatives
      dd: ['\\mathrm{d}#1', 1],
      dv: ['\\frac{\\mathrm{d} #1}{\\mathrm{d} #2}', 2],
      pdv: ['\\frac{\\partial #1}{\\partial #2}', 2],
      fdv: ['\\frac{\\delta #1}{\\delta #2}', 2],

      // Physics notation
      bra: ['\\langle #1 |', 1],
      ket: ['| #1 \\rangle', 1],
      braket: ['\\langle #1 | #2 \\rangle', 2],
      expval: ['\\langle #1 \\rangle', 1],

      // Bold vectors
      vb: ['\\mathbf{#1}', 1],
      va: ['\\vec{\\mathbf{#1}}', 1],
      vu: ['\\hat{\\mathbf{#1}}', 1],

      // Planck units - Central to Omega-Theory
      lP: '\\ell_P',
      tP: 't_P',
      mP: 'm_P',
      EP: 'E_P',
      LP: '\\ell_P',

      // Spacetime lattice
      Lat: '\\Lambda',
      ZZ: '\\mathbb{Z}',
      RR: '\\mathbb{R}',
      CC: '\\mathbb{C}',
      NN: '\\mathbb{N}',
      QQ: '\\mathbb{Q}',

      // Information current (Fourth Noether Law)
      JI: 'J^\\mu_I',
      divJ: '\\partial_\\mu J^\\mu_I',

      // Action density
      rhoS: '\\rho_S',

      // Christoffel symbols
      Gamma: ['\\Gamma^{#1}_{#2#3}', 3],
      Chris: ['\\Gamma^{#1}_{#2#3}', 3],

      // Covariant derivative
      nabla: '\\nabla',
      covD: ['\\nabla_{#1}', 1],

      // Metric
      gab: 'g_{\\mu\\nu}',
      gup: 'g^{\\mu\\nu}',

      // Curvature tensors
      Riemann: 'R^{\\rho}_{\\sigma\\mu\\nu}',
      Ricci: 'R_{\\mu\\nu}',
      RicciScalar: 'R',

      // Torsion (Einstein-Cartan)
      Torsion: 'T^{\\lambda}_{\\mu\\nu}',
      Contorsion: 'K^{\\lambda}_{\\mu\\nu}',

      // Common expressions
      half: '\\frac{1}{2}',
      third: '\\frac{1}{3}',
      quarter: '\\frac{1}{4}',

      // QM operators
      Hhat: '\\hat{H}',
      phat: '\\hat{p}',
      xhat: '\\hat{x}',

      // Order notation
      order: ['\\mathcal{O}\\left(#1\\right)', 1],
      bigO: ['\\mathcal{O}\\left(#1\\right)', 1],

      // Sets
      setR: '\\mathbb{R}',
      setC: '\\mathbb{C}',
      setZ: '\\mathbb{Z}',
      setN: '\\mathbb{N}',
      setQ: '\\mathbb{Q}',

      // Common physics
      hbar: '\\hbar',
      kB: 'k_B',

      // Differential geometry
      tensor: ['#1^{#2}_{#3}', 3],
      metric: 'g_{\\mu\\nu}',
      connection: '\\Gamma',

      // Box for important equations
      boxedeq: ['\\boxed{#1}', 1]
    },

    // Equation numbering
    tags: 'ams',
    tagSide: 'right',
    tagIndent: '0.8em',

    // Environments
    environments: {
      theorem: ['\\begin{theorem}', '\\end{theorem}'],
      proof: ['\\begin{proof}', '\\end{proof}'],
      definition: ['\\begin{definition}', '\\end{definition}']
    }
  },

  // Options
  options: {
    skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code'],
    ignoreHtmlClass: 'tex2jax_ignore|no-mathjax',
    processHtmlClass: 'tex2jax_process|mathjax'
  },

  // SVG output (best quality)
  svg: {
    fontCache: 'global',
    scale: 1,
    minScale: 0.5
  },

  // CHTML output (faster)
  chtml: {
    scale: 1,
    minScale: 0.5,
    matchFontHeight: true
  },

  // Startup
  startup: {
    pageReady: () => {
      return MathJax.startup.defaultPageReady().then(() => {
        console.log('MathJax typesetting complete for Omega-Theory');
      });
    }
  }
};

// Initialize MathJax when document is ready
document$.subscribe(() => {
  MathJax.typesetPromise();
});
