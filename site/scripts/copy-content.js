/**
 * Copy physics papers to Astro content directory
 * Adds frontmatter where needed
 */

import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const rootDir = path.resolve(__dirname, '../..');

const papersSourceDir = path.join(rootDir, 'PhysicsPapers');
const papersDestDir = path.join(__dirname, '../src/content/papers');

// Paper metadata - updated to match actual files
const papersMeta = {
  // Core Theory
  'Main-Paper-Postulates.md': {
    title: 'Main Paper: How This Started',
    description: 'The origin story and central thesis of Omega-Theory',
    category: 'Core Theory',
    order: 1,
  },
  'unified-theory-diagram.md': {
    title: 'Visual Summary: The Complete Causal Architecture',
    description: '11-level diagram showing how everything connects',
    category: 'Core Theory',
    order: 2,
  },
  'Complete-Omega-Theory-Unified-Framework.md': {
    title: 'Complete Omega-Theory Unified Framework',
    description: 'Full technical treatment with all equations',
    category: 'Core Theory',
    order: 3,
  },
  'KeyInsight-Irrationals-Action-Thresholds.md': {
    title: 'Key Insight: Irrationals and Action Thresholds',
    description: 'The core mechanism of discrete spacetime',
    category: 'Core Theory',
    order: 4,
  },

  // Appendices (actual files)
  'Appendix-A-Action-Density-and-Quantum-Errors.md': {
    title: 'Appendix A: Action Density and Quantum Errors',
    description: 'Connecting action density to quantum error rates',
    category: 'Appendices',
    order: 10,
  },
  'Appendix-B-Quantum-Computing-Temperature-Limits.md': {
    title: 'Appendix B: Quantum Computing Temperature Limits',
    description: 'Temperature constraints on quantum computation',
    category: 'Appendices',
    order: 11,
  },
  'Appendix-C-Catalog-of-Evolution-Functionals.md': {
    title: 'Appendix C: Catalog of Evolution Functionals',
    description: 'Mathematical catalog of evolution operators',
    category: 'Appendices',
    order: 12,
  },
  'Appendix-D-Topological-Surgery-And-Information-Healing.md': {
    title: 'Appendix D: Topological Surgery and Information Healing',
    description: 'The mathematical backbone of the theory',
    category: 'Appendices',
    order: 13,
  },
  'Appendix-E-Quantum-Entanglement-Dimensional-Theory.md': {
    title: 'Appendix E: Quantum Entanglement Dimensional Theory',
    description: 'Entanglement and dimensional reduction',
    category: 'Appendices',
    order: 14,
  },
  'appendix-E-visual-diagrams.md': {
    title: 'Appendix E: Visual Diagrams',
    description: 'Visual representations of key concepts',
    category: 'Appendices',
    order: 15,
  },
  'Appendix-F-Information-Flow-Conservation.md': {
    title: 'Appendix F: Information Flow Conservation',
    description: 'The Fourth Noether Law',
    category: 'Appendices',
    order: 16,
  },
  'Appendix-G-Graviton-Predictions.md': {
    title: 'Appendix G: Graviton Predictions',
    description: 'Predictions for graviton properties',
    category: 'Appendices',
    order: 17,
  },
  'Appendix-H-Renormalization-Correspondence.md': {
    title: 'Appendix H: Renormalization Correspondence',
    description: 'Connecting discrete and continuous renormalization',
    category: 'Appendices',
    order: 18,
  },
  'Appendix-I-Experimental-Tests.md': {
    title: 'Appendix I: Experimental Tests',
    description: '21 testable predictions',
    category: 'Appendices',
    order: 19,
  },
  'Appendix-LorentzDopplerEquivalence.md': {
    title: 'Appendix L: Lorentz-Doppler Equivalence',
    description: 'Connecting Lorentz transformations and Doppler effects',
    category: 'Appendices',
    order: 21,
  },
  'Appendix-P-Einstein-Cartan-Torsion-Integration.md': {
    title: 'Appendix P: Einstein-Cartan Torsion Integration',
    description: 'Integrating torsion into the framework',
    category: 'Appendices',
    order: 25,
  },
  'Appendix-S-Stable-Wormholes-And-Chronology-Protection.md': {
    title: 'Appendix S: Stable Wormholes and Chronology Protection',
    description: 'Why time travel is impossible',
    category: 'Appendices',
    order: 28,
  },

  // Advanced
  'ErdosLagrangianUnification.md': {
    title: 'Erdős Lagrangian Unification',
    description: 'Unifying physics through Lagrangian formalism',
    category: 'Advanced',
    order: 50,
  },
};

// Files to skip (not papers)
const skipFiles = [
  'README.md',
  'README-Document-Structure.md',
];

function ensureDir(dir) {
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
}

function addFrontmatter(content, meta) {
  const frontmatter = `---
title: "${meta.title}"
${meta.description ? `description: "${meta.description}"` : ''}
${meta.category ? `category: "${meta.category}"` : ''}
${meta.order ? `order: ${meta.order}` : ''}
---

`;

  // Check if file already has frontmatter
  if (content.startsWith('---')) {
    return content;
  }

  return frontmatter + content;
}

function copyPapers() {
  ensureDir(papersDestDir);

  const files = fs.readdirSync(papersSourceDir);

  let copied = 0;
  let skipped = 0;

  for (const file of files) {
    if (!file.endsWith('.md')) continue;
    if (skipFiles.includes(file)) {
      console.log(`⏭ Skipped: ${file}`);
      skipped++;
      continue;
    }

    const sourcePath = path.join(papersSourceDir, file);
    const stats = fs.statSync(sourcePath);

    if (!stats.isFile()) continue;

    let content = fs.readFileSync(sourcePath, 'utf-8');

    // Get metadata or create default
    const meta = papersMeta[file] || {
      title: file.replace('.md', '').replace(/-/g, ' '),
      category: 'Papers',
    };

    content = addFrontmatter(content, meta);

    // Create slug from filename
    const slug = file.toLowerCase().replace('.md', '');
    const destPath = path.join(papersDestDir, slug + '.md');

    fs.writeFileSync(destPath, content);
    console.log(`✓ Copied: ${file} -> ${slug}.md`);
    copied++;
  }

  console.log(`\nSummary: ${copied} papers copied, ${skipped} files skipped`);
}

console.log('Copying physics papers to content directory...\n');
copyPapers();
console.log('\nDone!');
