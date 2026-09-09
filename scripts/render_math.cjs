'use strict';
// Build-time only. The generated website needs neither JavaScript nor KaTeX to read mathematics.
const fs = require('node:fs');
const path = require('node:path');
const katex = require(path.join(__dirname, '..', 'third_party', 'katex', 'katex.min.js'));
try {
  if (katex.version !== '0.16.22') throw new Error(`Expected KaTeX 0.16.22, found ${katex.version}.`);
  const input = JSON.parse(fs.readFileSync(0, 'utf8'));
  if (!Array.isArray(input) || input.some(x => typeof x !== 'string')) {
    throw new Error('Expected an array of LaTeX strings.');
  }
  const output = input.map((tex, index) => {
    try {
      return katex.renderToString(tex, {output: 'mathml', displayMode: true,
        throwOnError: true, strict: 'error', trust: false});
    } catch (error) { throw new Error(`Formula ${index + 1}: ${error.message}`); }
  });
  process.stdout.write(JSON.stringify(output));
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exitCode = 1;
}
