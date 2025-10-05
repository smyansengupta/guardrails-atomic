import { NLToYAMLError } from '@/lib/utils/errors';
import { generateWithOpenRouter } from '@/lib/services/openrouter.service';
import { parseSpec } from '@/lib/core/spec-parser';
import { readFile } from 'fs/promises';
import path from 'path';

/**
 * Result from NL to YAML generation
 */
export interface NLToYAMLResult {
  yaml: string;
  warnings?: string[];
}

/**
 * Generate YAML specification from natural language description
 *
 * @param description - Natural language description of the desired handler
 * @param context - Optional additional context about the system
 * @returns Generated YAML spec and optional warnings
 * @throws NLToYAMLError if generation fails
 */
export async function generateYAMLFromNL(
  description: string,
  context?: string
): Promise<NLToYAMLResult> {
  try {
    // 1. Load the NL-to-YAML prompt template
    const templatePath = path.join(
      process.cwd(),
      'templates',
      'prompts',
      'spec-generation.txt'
    );
    let template = await readFile(templatePath, 'utf-8');

    // 2. Populate template with description and context
    const naturalLanguageInput = context
      ? `${description}\n\nAdditional Context: ${context}`
      : description;

    const prompt = template.replace('{{naturalLanguage}}', naturalLanguageInput);

    // 3. Call OpenRouter API to generate YAML
    const response = await generateWithOpenRouter(prompt);

    // 4. Extract YAML from markdown if wrapped
    const yamlMatch = response.match(/```yaml\n([\s\S]*?)\n```/);
    const yaml = yamlMatch ? yamlMatch[1] : response;

    // 5. Validate generated YAML
    const warnings: string[] = [];

    try {
      // Try to parse the generated YAML to validate it
      parseSpec(yaml);
    } catch (error) {
      // If parsing fails, add a warning but still return the YAML
      warnings.push(
        'Generated YAML may need manual review. Please verify all fields are correct.'
      );
    }

    // 6. Check for common issues and add warnings
    if (!yaml.includes('bounds:')) {
      warnings.push('Bounds may need to be adjusted for your use case.');
    }

    if (!yaml.includes('invariants:')) {
      warnings.push('No invariants were specified. Consider adding invariants for correctness.');
    }

    return {
      yaml: yaml.trim(),
      warnings: warnings.length > 0 ? warnings : undefined,
    };
  } catch (error) {
    if (error instanceof Error) {
      throw new NLToYAMLError(`Failed to generate YAML from description: ${error.message}`);
    }
    throw new NLToYAMLError('Failed to generate YAML from description');
  }
}
