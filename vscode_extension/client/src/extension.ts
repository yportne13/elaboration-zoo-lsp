/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import { ExtensionContext, Uri, window, workspace, commands, LogOutputChannel, Position, StatusBarItem, StatusBarAlignment, Disposable } from 'vscode';
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
// The initial size must cover the linker's main-thread stack (`-zstack-size`,
// stack-first layout) plus data and the startup heap: 64 MiB stack + headroom.
// 2 GiB max leaves headroom for the twin engine's resident state (~730 MB
// peak measured natively, vs ~200 MB for the reference engine).
const WASM_INITIAL_PAGES = 2048; // 134,217,728 bytes
const WASM_MAX_PAGES = 32768; // 2,147,483,648 bytes

async function startLanguageServer(
	context: ExtensionContext,
	wasm: Wasm,
): Promise<LanguageClient> {
	if (!channel) {
		channel = window.createOutputChannel('TyportHDL Language Server', { log: true });
		trackServerActivity(channel);
	}
	const serverOptions: ServerOptions = async () => {
		// Re-read on every (re)start so a settings change to the `reference`
		// escape hatch takes effect on the restart that follows it.
		const engine = readEngine('wasm');
		const options: ProcessOptions = {
			stdio: createStdioOptions(),
			mountPoints: [
				{ kind: 'workspaceFolder' },
			],
			// Pass the engine explicitly: the server's own default is the twin,
			// and this is the only channel that can select `reference`.
			env: { TYPORT_LSP_ENGINE: engine },
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
async function restartLanguageServer(context: ExtensionContext, wasm: Wasm): Promise<void> {
	if (client) {
		await client.stop();
	}
	updateStatusBar(State.Starting);
	client = await startLanguageServer(context, wasm);
	client.onDidChangeState((e) => {
		updateStatusBar(e.newState);
	});
	updateStatusBar(State.Running);
	watchServerLiveness(context, wasm);
}

// ── Liveness watchdog ───────────────────────────────────────────────────────

const PingRequest = new RequestType<null, boolean, void>('typort-hdl/ping');
// ~2 minutes of unanswered probes before reporting: long enough that a busy
// server (a slow prelude prime queues the probe; it is answered as soon as the
// main loop returns) is never mistaken for a dead one.
const WATCHDOG_INTERVAL_MS = 20000;
const WATCHDOG_TIMEOUT_MS = 10000;
const WATCHDOG_MISSES = 6;

let watchdog: Disposable | undefined;

/** Timestamp of the last sign of life from the server (probe or log line). */
let lastServerActivity = Date.now();

/**
 * Count every message the server writes to the output channel as a sign of
 * life, so a server that is busy (a long prelude prime emits no log line for a
 * while but is answering probes as soon as it returns to its main loop) is
 * never reported as dead.
 */
function trackServerActivity(channel: LogOutputChannel): void {
	for (const method of ['append', 'appendLine'] as const) {
		const original = channel[method].bind(channel);
		// eslint-disable-next-line @typescript-eslint/no-explicit-any
		(channel as any)[method] = (...args: unknown[]) => {
			lastServerActivity = Date.now();
			// eslint-disable-next-line @typescript-eslint/no-explicit-any
			return (original as any)(...args);
		};
	}
}

function withTimeout<T>(p: Promise<T>, ms: number): Promise<T> {
	return new Promise<T>((resolve, reject) => {
		const timer = setTimeout(() => reject(new Error(`no response within ${ms}ms`)), ms);
		p.then(
			(value) => { clearTimeout(timer); resolve(value); },
			(error) => { clearTimeout(timer); reject(error); },
		);
	});
}

/**
 * Trailing-edge liveness probe for the wasm backend.
 *
 * A guest that dies — a wasm trap such as an allocation failure against the
 * module's linear-memory ceiling — produces no close and no error event:
 * `process.run()` never settles, so `@vscode/wasm-wasi-lsp` never fires end or
 * error, the language client keeps its connection open, and the status bar
 * goes on claiming the server is running while nothing is served.  Probing the
 * main loop turns that silent death into a message in the output channel plus
 * a restart prompt.
 */
function watchServerLiveness(context: ExtensionContext, wasm: Wasm): void {
	watchdog?.dispose();
	const watched = client;
	if (!watched) {
		return;
	}
	let misses = 0;
	let reported = false;
	watchdog = new Disposable(() => clearInterval(timer));
	const timer = setInterval(async () => {
		if (reported || client !== watched) {
			return;
		}
		try {
			await withTimeout(watched.sendRequest(PingRequest, null), WATCHDOG_TIMEOUT_MS);
			misses = 0;
			lastServerActivity = Date.now();
		} catch {
			misses += 1;
			// Any server log line resets the expectation: only a server that is
			// silent *and* not answering is treated as gone.
			if (misses < WATCHDOG_MISSES || Date.now() - lastServerActivity < WATCHDOG_MISSES * WATCHDOG_INTERVAL_MS) {
				return;
			}
			reported = true;
			updateStatusBar(State.Stopped);
			channel.error(
				`TyportHDL: the language server has not answered ${misses} liveness probes in a row ` +
				`(${Math.round(misses * WATCHDOG_INTERVAL_MS / 1000)}s). A wasm guest that hits the module's ` +
				`linear-memory ceiling dies without reporting an error, so restart the server to recover.`,
			);
			const pick = await window.showWarningMessage(
				'TyportHDL: the language server stopped responding.',
				'Restart Language Server',
				'Show Log',
			);
			if (pick === 'Restart Language Server') {
				await restartLanguageServer(context, wasm);
			} else if (pick === 'Show Log') {
				channel.show();
			}
		}
	}, WATCHDOG_INTERVAL_MS);
	context.subscriptions.push(watchdog);
}

// ── Activation ──────────────────────────────────────────────────────────────

export interface ActivateOptions {
	/**
	 * Desktop hosts can spawn the external CLI server, so the action picker
	 * offers switching the backend. The web host cannot.
	 */
	canUseCli?: boolean;
}

export async function activate(context: ExtensionContext, options: ActivateOptions = {}) {
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
	watchServerLiveness(context, wasm);

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
		await restartLanguageServer(context, wasm);
		window.showInformationMessage('TyportHDL Language Server restarted.');
	}));

	// ── Status bar actions ────────────────────────────────────────────────

	context.subscriptions.push(commands.registerCommand('typort-hdl.showServerActions', () => {
		if (!client) return;
		return showServerActions({
			backend: 'wasm',
			canUseCli: options.canUseCli ?? false,
			restart: () => restartLanguageServer(context, wasm),
			showLog: () => channel.show(),
		});
	}));
}

export function deactivate(): Promise<void> | void {
	if (client) {
		return client.stop();
	}
}
