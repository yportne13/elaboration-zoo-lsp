import 'vscode-languageclient/node';
import { ExtensionContext, window, workspace, commands, StatusBarItem, StatusBarAlignment } from 'vscode';
import { LanguageClient, LanguageClientOptions, State } from 'vscode-languageclient/node';
import { activate as activateWasm, deactivate as deactivateWasm } from './extension';

let client: LanguageClient | undefined;
let statusBarItem: StatusBarItem | undefined;

function updateStatusBar(state: State): void {
	if (!statusBarItem) return;
	switch (state) {
		case State.Starting:
			statusBarItem.text = '$(sync~spin) TyPort';
			statusBarItem.tooltip = 'Starting TyportHDL language server...';
			break;
		case State.Running:
			statusBarItem.text = '$(check) TyPort';
			statusBarItem.tooltip = 'TyportHDL language server running';
			break;
		case State.Stopped:
			statusBarItem.text = '$(warning) TyPort';
			statusBarItem.tooltip = 'TyportHDL language server stopped';
			break;
	}
}

export async function activate(context: ExtensionContext) {
	// Create shared status bar
	statusBarItem = window.createStatusBarItem(StatusBarAlignment.Left, 0);
	statusBarItem.name = 'TyportHDL Language Server';
	statusBarItem.text = '$(sync~spin) TyPort';
	statusBarItem.tooltip = 'Starting TyportHDL language server...';
	statusBarItem.command = 'typort-hdl.showServerActions';
	context.subscriptions.push(statusBarItem);
	statusBarItem.show();

	// Register shared commands
	context.subscriptions.push(commands.registerCommand('typort-hdl.showServerActions', async () => {
		if (!client) return;
		const pick = await window.showQuickPick([
			{ label: '$(debug-restart) Restart Language Server', description: 'Restart the TyportHDL language server' },
			{ label: '$(output) Show Log', description: 'Open the language server output channel' },
		], { placeHolder: 'Language Server Actions' });
		if (!pick) return;
		if (pick.label.includes('Restart')) {
			commands.executeCommand('typort-hdl.restartLanguageServer');
		} else if (pick.label.includes('Log')) {
			const channel = window.createOutputChannel('TyportHDL Language Server', { log: true });
			channel.show();
		}
	}));

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

		updateStatusBar(State.Starting);
		client = new LanguageClient('lspClient', 'LSP Client', { command, args: ['lsp'] }, clientOptions);
		client.onDidChangeState((e) => updateStatusBar(e.newState));
		try {
			await client.start();
		} catch (error) {
			client.error(`Start failed`, error, 'force');
		}
		updateStatusBar(State.Running);

		context.subscriptions.push(commands.registerCommand('typort-hdl.restartLanguageServer', async () => {
			if (client) {
				await client.stop();
			}
			updateStatusBar(State.Starting);
			client = new LanguageClient('lspClient', 'LSP Client', { command, args: ['lsp'] }, clientOptions);
			client.onDidChangeState((e) => updateStatusBar(e.newState));
			try {
				await client.start();
			} catch (error) {
				client.error(`Start failed`, error, 'force');
			}
			updateStatusBar(State.Running);
			window.showInformationMessage('TyportHDL Language Server restarted.');
		}));
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
