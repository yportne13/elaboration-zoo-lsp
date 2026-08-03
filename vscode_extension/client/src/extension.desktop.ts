import 'vscode-languageclient/node';
import { ExtensionContext, window, workspace, commands, StatusBarItem, StatusBarAlignment, LogOutputChannel } from 'vscode';
import { LanguageClient, LanguageClientOptions, State, StateChangeEvent, ErrorAction, CloseAction } from 'vscode-languageclient/node';
import { activate as activateWasm, deactivate as deactivateWasm } from './extension';

// Maximum number of consecutive unexpected server exits before we stop
// retrying automatically and ask the user to restart the server manually.
const MAX_CONSECUTIVE_CRASHES = 5;
// Delay before restarting a crashed server to avoid a crash-restart storm.
const AUTO_RESTART_DELAY_MS = 1000;

let client: LanguageClient | undefined;
let statusBarItem: StatusBarItem | undefined;
let logChannel: LogOutputChannel | undefined;

// CLI server settings, resolved once in activate().
let cliCommand = 'typort';
let cliArgs: string[] = ['lsp'];
let cliClientOptions: LanguageClientOptions | undefined;

// Number of consecutive unexpected server exits. Reset to 0 whenever the
// server successfully reaches State.Running (automatic or manual restart).
let consecutiveCrashCount = 0;
// True while a stop is user-initiated (manual restart command / extension
// deactivation). Such stops must not be treated as crashes.
let userStopped = false;
// Pending auto-restart timer after an unexpected server exit.
let restartTimer: ReturnType<typeof setTimeout> | undefined;

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
		case State.StartFailed:
			statusBarItem.text = '$(error) TyPort';
			statusBarItem.tooltip = 'TyportHDL language server failed to start';
			break;
	}
}

/**
 * Creates a fresh LanguageClient for the CLI server and starts it.
 * Shared by the initial activation, the manual restart command and the
 * automatic restart after a server crash.
 */
async function startClient(): Promise<void> {
	if (!cliClientOptions) return;
	updateStatusBar(State.Starting);
	const newClient = new LanguageClient('lspClient', 'LSP Client', { command: cliCommand, args: cliArgs }, cliClientOptions);
	newClient.onDidChangeState(handleStateChange);
	client = newClient;
	try {
		await newClient.start();
	} catch (error) {
		newClient.error(`Start failed`, error, 'force');
	}
	if (newClient.state === State.Running) {
		updateStatusBar(State.Running);
	}
}

/**
 * Reacts to language client state changes: updates the status bar, resets the
 * consecutive crash counter on a successful start and, on an unexpected stop
 * (server crash), schedules an automatic restart (up to 5 consecutive times).
 */
function handleStateChange(e: StateChangeEvent): void {
	updateStatusBar(e.newState);

	if (e.newState === State.Running) {
		// A server that (re)started successfully breaks the chain of
		// consecutive crashes.
		consecutiveCrashCount = 0;
		return;
	}
	if (e.newState !== State.Stopped) {
		return;
	}

	// From here on the server stopped. Distinguish an unexpected exit (crash)
	// from a stop we triggered ourselves.
	if (userStopped) {
		return;
	}
	if (restartTimer !== undefined) {
		return; // A restart is already scheduled.
	}

	consecutiveCrashCount += 1;
	if (consecutiveCrashCount >= MAX_CONSECUTIVE_CRASHES) {
		logChannel?.appendLine(`Server exited unexpectedly ${MAX_CONSECUTIVE_CRASHES} times in a row. Stopping automatic restarts; please restart the language server manually.`);
		void window.showErrorMessage(
			'TyportHDL language server crashed 5 times in a row. Please restart it manually.',
			'Restart'
		).then((action) => {
			if (action === 'Restart') {
				void commands.executeCommand('typort-hdl.restartLanguageServer');
			}
		});
		return;
	}

	logChannel?.appendLine(`Server exited unexpectedly, restarting (attempt ${consecutiveCrashCount}/${MAX_CONSECUTIVE_CRASHES})...`);
	updateStatusBar(State.Starting);
	restartTimer = setTimeout(() => {
		restartTimer = undefined;
		void startClient();
	}, AUTO_RESTART_DELAY_MS);
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
			logChannel?.show();
		}
	}));

	const config = workspace.getConfiguration('typort-hdl');
	const mode = config.get<string>('lsp-mode', 'wasm');

	if (mode === 'cli') {
		cliCommand = config.get<string>('cli-server.path', '') || 'typort';
		cliArgs = ['lsp'];
		logChannel = window.createOutputChannel('TyportHDL Language Server', { log: true });
		logChannel.appendLine(`Starting CLI language server: ${cliCommand} lsp`);

		cliClientOptions = {
			documentSelector: [{ language: "typort" }],
			outputChannel: logChannel,
			errorHandler: {
				error: (_error, _message, count) => {
					// Match the library default: tolerate up to 3 consecutive
					// connection errors before shutting the server down.
					if (count !== undefined && count <= 3) {
						return { action: ErrorAction.Continue };
					}
					return { action: ErrorAction.Shutdown };
				},
				closed: () => {
					// Never let the library restart the server by itself: the
					// built-in restart has no consecutive-crash limit and no
					// delay, which would conflict with the restart logic here.
					// All restarts are managed via handleStateChange.
					return { action: CloseAction.DoNotRestart, message: 'Language server process exited', handled: true };
				},
			},
		};

		await startClient();

		context.subscriptions.push(commands.registerCommand('typort-hdl.restartLanguageServer', async () => {
			// The user takes control: cancel any pending automatic restart and
			// break the chain of consecutive crashes.
			if (restartTimer !== undefined) {
				clearTimeout(restartTimer);
				restartTimer = undefined;
			}
			consecutiveCrashCount = 0;
			// Mark the stop as user-initiated so that it is not counted as a
			// crash by handleStateChange.
			userStopped = true;
			try {
				if (client) {
					try {
						await client.stop();
					} catch (error) {
						client.error(`Stopping server failed`, error, 'force');
					}
				}
			} finally {
				userStopped = false;
			}
			await startClient();
			window.showInformationMessage('TyportHDL Language Server restarted.');
		}));
	} else {
		await activateWasm(context);
	}
}

export function deactivate() {
	if (client) {
		// The extension is going down: cancel a pending automatic restart and
		// mark the final stop as user-initiated so no restart is attempted.
		if (restartTimer !== undefined) {
			clearTimeout(restartTimer);
			restartTimer = undefined;
		}
		userStopped = true;
		return client.stop();
	}
	return deactivateWasm();
}
