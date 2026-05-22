/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import { ExtensionContext, Uri, window, workspace, commands, OutputChannel } from 'vscode';
import { LanguageClient, LanguageClientOptions, ServerOptions, RequestType } from 'vscode-languageclient';
import { Wasm, ProcessOptions } from '@vscode/wasm-wasi';
import { createStdioOptions, createUriConverters, startServer } from '@vscode/wasm-wasi-lsp';

let client: LanguageClient | undefined;
let channel: OutputChannel;

async function startLanguageServer(context: ExtensionContext, wasm: Wasm): Promise<LanguageClient> {
	if (!channel) {
		channel = window.createOutputChannel('TyportHDL Language Server');
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

export async function activate(context: ExtensionContext) {
	const wasm: Wasm = await Wasm.load();

	client = await startLanguageServer(context, wasm);

	// Register a text content provider for builtin:// URIs (e.g., prelude files).
	// When the user navigates to a builtin:// URI via go-to-definition, VS Code
	// calls this provider to get the file content instead of reading from disk.
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

	context.subscriptions.push(commands.registerCommand('typort-hdl.restartLanguageServer', async () => {
		if (client) {
			await client.stop();
		}
		client = await startLanguageServer(context, wasm);
		window.showInformationMessage('TyportHDL Language Server restarted.');
	}));
}

export function deactivate(): Promise<void> | void {
	if (client) {
		return client.stop();
	}
}
