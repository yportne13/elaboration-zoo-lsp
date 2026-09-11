/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import { ExtensionContext, Uri, window, workspace, commands, LogOutputChannel, Position, StatusBarItem, StatusBarAlignment } from 'vscode';
import { LanguageClient, LanguageClientOptions, ServerOptions, RequestType, State } from 'vscode-languageclient';
import { Wasm } from '@vscode/wasm-wasi/v1';
import type { ProcessOptions } from '@vscode/wasm-wasi/v1';
import { createStdioOptions, createUriConverters, startServer } from '@vscode/wasm-wasi-lsp';
import { readEngine, showServerActions } from './serverActions';

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

// The WASM module's linear memory, in 64 KiB pages. Must match the linker's
// `--initial-memory` / `--max-memory` in the extension's `npm run build`
// (vscode_extension/package.json): the wasm32-wasip1-threads module imports a
// shared memory with those exact bounds, so a mismatch fails instantiation.
// 2 GiB max leaves headroom for the twin engine's resident state (~730 MB
// peak measured natively, vs ~200 MB for the reference engine).
const WASM_INITIAL_PAGES = 640; // 41,943,040 bytes
const WASM_MAX_PAGES = 32768; // 2,147,483,648 bytes

async function startLanguageServer(
	context: ExtensionContext,
	wasm: Wasm,
	canUseTwin: boolean,
): Promise<LanguageClient> {
	if (!channel) {
		channel = window.createOutputChannel('TyportHDL Language Server', { log: true });
	}
	const serverOptions: ServerOptions = async () => {
		const engine = canUseTwin ? readEngine() : 'reference';
		const options: ProcessOptions = {
			stdio: createStdioOptions(),
			mountPoints: [
				{ kind: 'workspaceFolder' },
			],
			// The WASM guest reads this through `Engine::from_env`; without it
			// the server always elaborates with the reference engine.
			env: engine === 'twin' ? { TYPORT_LSP_ENGINE: 'twin' } : undefined,
		};
		const filename = Uri.joinPath(context.extensionUri, 'client', 'server.wasm');
		const bits = await workspace.fs.readFile(filename);
		const module = await WebAssembly.compile(bits);
		const process = await wasm.createProcess(
			'lsp-server',
			module,
			{ initial: WASM_INITIAL_PAGES, maximum: WASM_MAX_PAGES, shared: true },
			options,
		);

		const decoder = new TextDecoder('utf-8');
		process.stderr!.onData((data) => {
			channel.append(decoder.decode(data));
		});

		return startServer(process);
	};

	const clientOptions: LanguageClientOptions = {
		documentSelector: [{ language: "typort" }],
		outputChannel: channel,
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

/** Stop the running client and start a fresh one (status bar + command). */
async function restartLanguageServer(context: ExtensionContext, wasm: Wasm, canUseTwin: boolean): Promise<void> {
	if (client) {
		await client.stop();
	}
	updateStatusBar(State.Starting);
	client = await startLanguageServer(context, wasm, canUseTwin);
	client.onDidChangeState((e) => {
		updateStatusBar(e.newState);
	});
	updateStatusBar(State.Running);
}

// ── Activation ──────────────────────────────────────────────────────────────

export interface ActivateOptions {
	/**
	 * Desktop hosts can spawn the external CLI server, so the action picker
	 * offers switching the backend. The web host cannot.
	 */
	canUseCli?: boolean;
	/**
	 * Whether the twin engine may be selected. Both desktop backends support
	 * it (the WASM module reads `TYPORT_LSP_ENGINE`); the web host is kept on
	 * the reference engine.
	 */
	canUseTwin?: boolean;
}

export async function activate(context: ExtensionContext, options: ActivateOptions = {}) {
	const wasm: Wasm = await Wasm.load();
	const canUseTwin = options.canUseTwin ?? false;

	// Status bar
	statusBarItem = createStatusBarItem();
	context.subscriptions.push(statusBarItem);
	statusBarItem.show();
	updateStatusBar(State.Starting);

	client = await startLanguageServer(context, wasm, canUseTwin);

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
		await restartLanguageServer(context, wasm, canUseTwin);
		window.showInformationMessage('TyportHDL Language Server restarted.');
	}));

	// ── Status bar actions ────────────────────────────────────────────────

	context.subscriptions.push(commands.registerCommand('typort-hdl.showServerActions', () => {
		if (!client) return;
		return showServerActions({
			backend: 'wasm',
			canUseCli: options.canUseCli ?? false,
			canUseTwin,
			restart: () => restartLanguageServer(context, wasm, canUseTwin),
			showLog: () => channel.show(),
		});
	}));
}

export function deactivate(): Promise<void> | void {
	if (client) {
		return client.stop();
	}
}
