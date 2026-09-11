// extension.js — VS Code client for the Infera language server.
'use strict'

const path = require('path')
const { workspace } = require('vscode')
const { LanguageClient, TransportKind } = require('vscode-languageclient/node')

let client

function activate(context) {
  const serverModule = context.asAbsolutePath(path.join('server', 'server.js'))
  const serverOptions = {
    run: { module: serverModule, transport: TransportKind.ipc },
    debug: { module: serverModule, transport: TransportKind.ipc, options: { execArgv: ['--nolazy', '--inspect=6009'] } }
  }
  const clientOptions = {
    documentSelector: [{ scheme: 'file', language: 'infera' }],
    synchronize: {
      configurationSection: 'infera',
      fileEvents: workspace.createFileSystemWatcher('**/{neoprolog,infera,nprolog}.conf')
    }
  }
  client = new LanguageClient('infera', 'Infera Language Server', serverOptions, clientOptions)
  client.start()
}

function deactivate() {
  return client ? client.stop() : undefined
}

module.exports = { activate, deactivate }
