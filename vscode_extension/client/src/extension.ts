/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import { ExtensionContext, Uri, window, workspace, commands, LogOutputChannel, Position, StatusBarItem, StatusBarAlignment } from 'vscode';
import { LanguageClient, LanguageClientOptions, ServerOptions, RequestType, State } from 'vscode-languageclient';
import { Wasm } from '@vscode/wasm-wasi/v1';
import type { ProcessOptions } from '@vscode/wasm-wasi/v1';
import { createStdioOptions, createUriConverters, startServer } from '@vscode/wasm-wasi-lsp';

let client: LanguageClient | undefined;
let channel: LogOutputChannel;

// ── Status Bar ──────────────────────────────────────────────────────────────

let statusBarItem: StatusBarItem;

function createStatusBarItem(): StatusBarItem {
	const item = window.createStatusBarItem(StatusBarAlignment.Left, 0);
	item.name = 'TyportHDL Language Server';
	item.text = '$(sync~spin) TyPort';
	item.tooltip = 'Starting TyportHDL Language Server...';
	item.command = 'typort-hdl.showServerActions';
	return item;
}

function updateStatusBar(state: State): void {
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

// ── Server Start ────────────────────────────────────────────────────────────

async function startLanguageServer(context: ExtensionContext, wasm: Wasm): Promise<LanguageClient> {
	if (!channel) {
		channel = window.createOutputChannel('TyportHDL Language Server', { log: true });
	}
	const serverOptions: ServerOptions = async () => {
		const options: ProcessOptions = {
			stdio: createStdioOptions(),
			mountPoints: [
				{ kind: 'workspaceFolder' },
			]
		};
		const filename = Uri.joinPath(context.extensionUri, 'client', 'server.wasm');
		const bits = await workspace.fs.readFile(filename);
		const module = await WebAssembly.compile(bits);
		const process = await wasm.createProcess('lsp-server', module, { initial: 640, maximum: 16000, shared: true }, options);

		const decoder = new TextDecoder('utf-8');
		process.stderr!.onData((data) => {
			channel.append(decoder.decode(data));
		});

		return startServer(process);
	};

	const clientOptions: LanguageClientOptions = {
		documentSelector: [{ language: "typort" }],
		outputChannel: channel,
		synchronize: {
			fileEvents: workspace.createFileSystemWatcher("**/.clientrc"),
		},
		uriConverters: createUriConverters(),
	};

	const newClient = new LanguageClient('lspClient', 'LSP Client', serverOptions, clientOptions);
	try {
		await newClient.start();
	} catch (error) {
		newClient.error(`Start failed`, error, 'force');
	}
	return newClient;
}

// ── Activation ──────────────────────────────────────────────────────────────

export async function activate(context: ExtensionContext) {
	const wasm: Wasm = await Wasm.load();

	// Status bar
	statusBarItem = createStatusBarItem();
	context.subscriptions.push(statusBarItem);
	statusBarItem.show();
	updateStatusBar(State.Starting);

	client = await startLanguageServer(context, wasm);

	// Track language client state changes → update status bar
	client.onDidChangeState((e) => {
		updateStatusBar(e.newState);
	});

	// After client is started, update to running state
	updateStatusBar(State.Running);

	// ── Builtin content provider ──────────────────────────────────────────

	const BuiltinContentRequest = new RequestType<{ uri: string }, string | null, void>('typort-hdl/builtinContent');
	context.subscriptions.push(
		workspace.registerTextDocumentContentProvider('builtin', {
			async provideTextDocumentContent(uri: Uri): Promise<string | undefined> {
				if (!client) {
					return undefined;
				}
				try {
					const content = await client.sendRequest(
						BuiltinContentRequest,
						{ uri: uri.toString() }
					);
					return content ?? undefined;
				} catch {
					return undefined;
				}
			}
		})
	);

	type CountFileParams = { folder: string };
	const CountFilesRequest = new RequestType<CountFileParams, number, void>('wasm-language-server/countFiles');
	context.subscriptions.push(commands.registerCommand('vscode-samples.wasm-language-server.countFiles', async () => {
		const folder = workspace.workspaceFolders![0].uri;
		const result = await client!.sendRequest(CountFilesRequest, { folder: client!.code2ProtocolConverter.asUri(folder) });
		window.showInformationMessage(`The workspace contains ${result} files.`);
	}));

	// ── Expand macro ──────────────────────────────────────────────────────

	type ExpandMacroParams = { uri: string; position: Position };
	type ExpandMacroResult = { name: string; range: { start: Position; end: Position }; expanded_text: string };
	const ExpandMacroRequest = new RequestType<ExpandMacroParams, ExpandMacroResult | null, void>('typort-hdl/expandMacro');
	context.subscriptions.push(commands.registerCommand('typort-hdl.expandMacro', async () => {
		const editor = window.activeTextEditor;
		if (!editor || !client) {
			return;
		}
		const uri = client.code2ProtocolConverter.asUri(editor.document.uri);
		const position = editor.selection.active;
		try {
			const result = await client.sendRequest(ExpandMacroRequest, { uri, position });
			if (result) {
				const doc = await workspace.openTextDocument({
					content: result.expanded_text,
					language: 'typort',
				});
				await window.showTextDocument(doc, { preview: true });
			} else {
				window.showInformationMessage('No macro expansion found at cursor position.');
			}
		} catch (error) {
			window.showErrorMessage(`Expand macro failed: ${error}`);
		}
	}));

	// ── Restart server ────────────────────────────────────────────────────

	context.subscriptions.push(commands.registerCommand('typort-hdl.restartLanguageServer', async () => {
		if (client) {
			await client.stop();
		}
		updateStatusBar(State.Starting);
		client = await startLanguageServer(context, wasm);
		client.onDidChangeState((e) => {
			updateStatusBar(e.newState);
		});
		updateStatusBar(State.Running);
		window.showInformationMessage('TyportHDL Language Server restarted.');
	}));

	// ── Status bar actions ────────────────────────────────────────────────

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
			channel.show();
		}
	}));
}

export function deactivate(): Promise<void> | void {
	if (client) {
		return client.stop();
	}
}
