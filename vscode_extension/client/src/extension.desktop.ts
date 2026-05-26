import 'vscode-languageclient/node';
import { ExtensionContext, window, workspace, LogOutputChannel } from 'vscode';
import { LanguageClient, LanguageClientOptions } from 'vscode-languageclient/node';
import { activate as activateWasm, deactivate as deactivateWasm } from './extension';

let client: LanguageClient | undefined;

export async function activate(context: ExtensionContext) {
	const config = workspace.getConfiguration('typort-hdl');
	const mode = config.get<string>('lsp-mode', 'wasm');

	if (mode === 'cli') {
		const command = config.get<string>('cli-server.path', '') || 'typort';
		const channel = window.createOutputChannel('TyportHDL Language Server', { log: true });
		channel.appendLine(`Starting CLI language server: ${command} lsp`);

		const clientOptions: LanguageClientOptions = {
			documentSelector: [{ language: "typort" }],
			outputChannel: channel,
			synchronize: {
				fileEvents: workspace.createFileSystemWatcher("**/.clientrc"),
			},
		};

		client = new LanguageClient('lspClient', 'LSP Client', { command, args: ['lsp'] }, clientOptions);
		try {
			await client.start();
		} catch (error) {
			client.error(`Start failed`, error, 'force');
		}
	} else {
		await activateWasm(context);
	}
}

export function deactivate() {
	if (client) {
		return client.stop();
	}
	return deactivateWasm();
}
