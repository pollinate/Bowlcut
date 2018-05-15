import commonjs from 'rollup-plugin-commonjs';
import nodeResolve from 'rollup-plugin-node-resolve';

export default {
  input: 'src/module.js',
  output: {
    file: 'dist/bundle.js',
    format: 'es'
  },
  plugins: [
    nodeResolve({
      main: true,
      browser: true,
      preferBuiltIns: false
    }),
    commonjs({
      include: 'node_modules/**'
    })
  ]
};
